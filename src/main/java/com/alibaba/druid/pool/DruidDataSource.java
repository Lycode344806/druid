/*
 * Copyright 1999-2018 Alibaba Group Holding Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.alibaba.druid.pool;

import static com.alibaba.druid.util.Utils.getBoolean;

import java.io.Closeable;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.StringTokenizer;
import java.util.TimeZone;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Future;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLongFieldUpdater;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import javax.management.JMException;
import javax.management.MBeanRegistration;
import javax.management.MBeanServer;
import javax.management.ObjectName;
import javax.naming.NamingException;
import javax.naming.Reference;
import javax.naming.Referenceable;
import javax.naming.StringRefAddr;
import javax.sql.ConnectionEvent;
import javax.sql.ConnectionEventListener;
import javax.sql.ConnectionPoolDataSource;
import javax.sql.PooledConnection;

import com.alibaba.druid.Constants;
import com.alibaba.druid.TransactionTimeoutException;
import com.alibaba.druid.VERSION;
import com.alibaba.druid.filter.AutoLoad;
import com.alibaba.druid.filter.Filter;
import com.alibaba.druid.filter.FilterChainImpl;
import com.alibaba.druid.mock.MockDriver;
import com.alibaba.druid.pool.DruidPooledPreparedStatement.PreparedStatementKey;
import com.alibaba.druid.pool.vendor.*;
import com.alibaba.druid.proxy.DruidDriver;
import com.alibaba.druid.proxy.jdbc.DataSourceProxyConfig;
import com.alibaba.druid.proxy.jdbc.TransactionInfo;
import com.alibaba.druid.sql.ast.SQLStatement;
import com.alibaba.druid.sql.ast.statement.SQLSelectQuery;
import com.alibaba.druid.sql.ast.statement.SQLSelectQueryBlock;
import com.alibaba.druid.sql.ast.statement.SQLSelectStatement;
import com.alibaba.druid.sql.parser.SQLParserUtils;
import com.alibaba.druid.sql.parser.SQLStatementParser;
import com.alibaba.druid.stat.DruidDataSourceStatManager;
import com.alibaba.druid.stat.JdbcDataSourceStat;
import com.alibaba.druid.stat.JdbcSqlStat;
import com.alibaba.druid.stat.JdbcSqlStatValue;
import com.alibaba.druid.support.logging.Log;
import com.alibaba.druid.support.logging.LogFactory;
import com.alibaba.druid.util.JMXUtils;
import com.alibaba.druid.util.JdbcConstants;
import com.alibaba.druid.util.JdbcUtils;
import com.alibaba.druid.util.StringUtils;
import com.alibaba.druid.util.Utils;
import com.alibaba.druid.wall.WallFilter;
import com.alibaba.druid.wall.WallProviderStatValue;

/**
 * @author ljw [ljw2083@alibaba-inc.com]
 * @author wenshao [szujobs@hotmail.com]
 */
public class DruidDataSource extends DruidAbstractDataSource implements DruidDataSourceMBean, ManagedDataSource, Referenceable, Closeable, Cloneable, ConnectionPoolDataSource, MBeanRegistration {

    private final static Log                 LOG                       = LogFactory.getLog(DruidDataSource.class);
    private static final long                serialVersionUID          = 1L;
    // stats
    private volatile long                    recycleErrorCount         = 0L;
    private long                             connectCount              = 0L;
    private long                             closeCount                = 0L;
    private volatile long                    connectErrorCount         = 0L;
    private long                             recycleCount              = 0L;
    private long                             removeAbandonedCount      = 0L;
    private long                             notEmptyWaitCount         = 0L;
    private long                             notEmptySignalCount       = 0L;
    private long                             notEmptyWaitNanos         = 0L;
    private int                              keepAliveCheckCount       = 0;
    private int                              activePeak                = 0;
    private long                             activePeakTime            = 0;
    private int                              poolingPeak               = 0;
    private long                             poolingPeakTime           = 0;
    // store
    private volatile DruidConnectionHolder[] connections;
    private int                              poolingCount              = 0;
    private int                              activeCount               = 0;
    private volatile long                    discardCount              = 0;
    private int                              notEmptyWaitThreadCount   = 0;
    private int                              notEmptyWaitThreadPeak    = 0;
    //
    private DruidConnectionHolder[]          evictConnections;
    private DruidConnectionHolder[]          keepAliveConnections;

    // threads
    private volatile ScheduledFuture<?>      destroySchedulerFuture;
    private DestroyTask                      destroyTask;

    private volatile Future<?>               createSchedulerFuture;

    private CreateConnectionThread           createConnectionThread;
    private DestroyConnectionThread          destroyConnectionThread;
    private LogStatsThread                   logStatsThread;
    private int                              createTaskCount;

    private volatile long                    createTaskIdSeed          = 1L;
    private long[]                           createTasks;

    private final CountDownLatch             initedLatch               = new CountDownLatch(2);

    private volatile boolean                 enable                    = true;

    private boolean                          resetStatEnable           = true;
    private volatile long                    resetCount                = 0L;

    private String                           initStackTrace;

    private volatile boolean                 closing                   = false;
    private volatile boolean                 closed                    = false;
    private long                             closeTimeMillis           = -1L;

    protected JdbcDataSourceStat             dataSourceStat;

    private boolean                          useGlobalDataSourceStat   = false;
    private boolean                          mbeanRegistered           = false;
    public static ThreadLocal<Long>          waitNanosLocal            = new ThreadLocal<Long>();
    private boolean                          logDifferentThread        = true;
    private volatile boolean                 keepAlive                 = false;
    private boolean                          asyncInit                 = false;
    protected boolean                        killWhenSocketReadTimeout = false;
    protected boolean                        checkExecuteTime          = false;

    private static List<Filter>              autoFilters               = null;
    private boolean                          loadSpifilterSkip         = false;
    private volatile DataSourceDisableException disableException       = null;

    protected static final AtomicLongFieldUpdater<DruidDataSource> recycleErrorCountUpdater
            = AtomicLongFieldUpdater.newUpdater(DruidDataSource.class, "recycleErrorCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> connectErrorCountUpdater
            = AtomicLongFieldUpdater.newUpdater(DruidDataSource.class, "connectErrorCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> resetCountUpdater
            = AtomicLongFieldUpdater.newUpdater(DruidDataSource.class, "resetCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> createTaskIdSeedUpdater
            = AtomicLongFieldUpdater.newUpdater(DruidDataSource.class, "createTaskIdSeed");

    public DruidDataSource(){
        this(false);
    }

    public DruidDataSource(boolean fairLock){
        super(fairLock);

        configFromPropety(System.getProperties());
    }

    public boolean isAsyncInit() {
        return asyncInit;
    }

    public void setAsyncInit(boolean asyncInit) {
        this.asyncInit = asyncInit;
    }

    public void configFromPropety(Properties properties) {
        {
            String property = properties.getProperty("druid.name");
            if (property != null) {
                this.setName(property);
            }
        }
        {
            String property = properties.getProperty("druid.url");
            if (property != null) {
                this.setUrl(property);
            }
        }
        {
            String property = properties.getProperty("druid.username");
            if (property != null) {
                this.setUsername(property);
            }
        }
        {
            String property = properties.getProperty("druid.password");
            if (property != null) {
                this.setPassword(property);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.testWhileIdle");
            if (value != null) {
                this.testWhileIdle = value;
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.testOnBorrow");
            if (value != null) {
                this.testOnBorrow = value;
            }
        }
        {
            String property = properties.getProperty("druid.validationQuery");
            if (property != null && property.length() > 0) {
                this.setValidationQuery(property);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useGlobalDataSourceStat");
            if (value != null) {
                this.setUseGlobalDataSourceStat(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useGloalDataSourceStat"); // compatible for early versions
            if (value != null) {
                this.setUseGlobalDataSourceStat(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.asyncInit"); // compatible for early versions
            if (value != null) {
                this.setAsyncInit(value);
            }
        }
        {
            String property = properties.getProperty("druid.filters");

            if (property != null && property.length() > 0) {
                try {
                    this.setFilters(property);
                } catch (SQLException e) {
                    LOG.error("setFilters error", e);
                }
            }
        }
        {
            String property = properties.getProperty(Constants.DRUID_TIME_BETWEEN_LOG_STATS_MILLIS);
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setTimeBetweenLogStatsMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property '" + Constants.DRUID_TIME_BETWEEN_LOG_STATS_MILLIS + "'", e);
                }
            }
        }
        {
            String property = properties.getProperty(Constants.DRUID_STAT_SQL_MAX_SIZE);
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    if (dataSourceStat != null) {
                        dataSourceStat.setMaxSqlSize(value);
                    }
                } catch (NumberFormatException e) {
                    LOG.error("illegal property '" + Constants.DRUID_STAT_SQL_MAX_SIZE + "'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.clearFiltersEnable");
            if (value != null) {
                this.setClearFiltersEnable(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.resetStatEnable");
            if (value != null) {
                this.setResetStatEnable(value);
            }
        }
        {
            String property = properties.getProperty("druid.notFullTimeoutRetryCount");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setNotFullTimeoutRetryCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.notFullTimeoutRetryCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.timeBetweenEvictionRunsMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setTimeBetweenEvictionRunsMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.timeBetweenEvictionRunsMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxWaitThreadCount");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxWaitThreadCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxWaitThreadCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxWait");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxWait(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxWait'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.failFast");
            if (value != null) {
                this.setFailFast(value);
            }
        }
        {
            String property = properties.getProperty("druid.phyTimeoutMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setPhyTimeoutMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.phyTimeoutMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.phyMaxUseCount");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setPhyMaxUseCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.phyMaxUseCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.minEvictableIdleTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setMinEvictableIdleTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.minEvictableIdleTimeMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxEvictableIdleTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setMaxEvictableIdleTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxEvictableIdleTimeMillis'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.keepAlive");
            if (value != null) {
                this.setKeepAlive(value);
            }
        }
        {
            String property = properties.getProperty("druid.keepAliveBetweenTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setKeepAliveBetweenTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.keepAliveBetweenTimeMillis'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.poolPreparedStatements");
            if (value != null) {
                this.setPoolPreparedStatements0(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.initVariants");
            if (value != null) {
                this.setInitVariants(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.initGlobalVariants");
            if (value != null) {
                this.setInitGlobalVariants(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useUnfairLock");
            if (value != null) {
                this.setUseUnfairLock(value);
            }
        }
        {
            String property = properties.getProperty("druid.driverClassName");
            if (property != null) {
                this.setDriverClassName(property);
            }
        }
        {
            String property = properties.getProperty("druid.initialSize");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setInitialSize(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.initialSize'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.minIdle");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMinIdle(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.minIdle'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxActive");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxActive(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxActive'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.killWhenSocketReadTimeout");
            if (value != null) {
                setKillWhenSocketReadTimeout(value);
            }
        }
        {
            String property = properties.getProperty("druid.connectProperties");
            if (property != null) {
                this.setConnectionProperties(property);
            }
        }
        {
            String property = properties.getProperty("druid.maxPoolPreparedStatementPerConnectionSize");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxPoolPreparedStatementPerConnectionSize(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxPoolPreparedStatementPerConnectionSize'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.initConnectionSqls");
            if (property != null && property.length() > 0) {
                try {
                    StringTokenizer tokenizer = new StringTokenizer(property, ";");
                    setConnectionInitSqls(Collections.list(tokenizer));
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.initConnectionSqls'", e);
                }
            }
        }
        {
            String property = System.getProperty("druid.load.spifilter.skip");
            if (property != null && !"false".equals(property)) {
                loadSpifilterSkip = true;
            }
        }
        {
            String property = System.getProperty("druid.checkExecuteTime");
            if (property != null && !"false".equals(property)) {
                checkExecuteTime = true;
            }
        }
    }

    public boolean isKillWhenSocketReadTimeout() {
        return killWhenSocketReadTimeout;
    }

    public void setKillWhenSocketReadTimeout(boolean killWhenSocketTimeOut) {
        this.killWhenSocketReadTimeout = killWhenSocketTimeOut;
    }

    public boolean isUseGlobalDataSourceStat() {
        return useGlobalDataSourceStat;
    }

    public void setUseGlobalDataSourceStat(boolean useGlobalDataSourceStat) {
        this.useGlobalDataSourceStat = useGlobalDataSourceStat;
    }

    public boolean isKeepAlive() {
        return keepAlive;
    }

    public void setKeepAlive(boolean keepAlive) {
        this.keepAlive = keepAlive;
    }

    public String getInitStackTrace() {
        return initStackTrace;
    }

    public boolean isResetStatEnable() {
        return resetStatEnable;
    }

    public void setResetStatEnable(boolean resetStatEnable) {
        this.resetStatEnable = resetStatEnable;
        if (dataSourceStat != null) {
            dataSourceStat.setResetStatEnable(resetStatEnable);
        }
    }

    public long getDiscardCount() {
        return discardCount;
    }

    public void restart() throws SQLException {
        lock.lock();
        try {
            if (activeCount > 0) {
                throw new SQLException("can not restart, activeCount not zero. " + activeCount);
            }
            if (LOG.isInfoEnabled()) {
                LOG.info("{dataSource-" + this.getID() + "} restart");
            }

            this.close();
            this.resetStat();
            this.inited = false;
            this.enable = true;
            this.closed = false;
        } finally {
            lock.unlock();
        }
    }

    public void resetStat() {
        if (!isResetStatEnable()) {
            return;
        }

        lock.lock();
        try {
            connectCount = 0;
            closeCount = 0;
            discardCount = 0;
            recycleCount = 0;
            createCount = 0L;
            directCreateCount = 0;
            destroyCount = 0L;
            removeAbandonedCount = 0;
            notEmptyWaitCount = 0;
            notEmptySignalCount = 0L;
            notEmptyWaitNanos = 0;

            activePeak = activeCount;
            activePeakTime = 0;
            poolingPeak = 0;
            createTimespan = 0;
            lastError = null;
            lastErrorTimeMillis = 0;
            lastCreateError = null;
            lastCreateErrorTimeMillis = 0;
        } finally {
            lock.unlock();
        }

        connectErrorCountUpdater.set(this, 0);
        errorCountUpdater.set(this, 0);
        commitCountUpdater.set(this, 0);
        rollbackCountUpdater.set(this, 0);
        startTransactionCountUpdater.set(this, 0);
        cachedPreparedStatementHitCountUpdater.set(this, 0);
        closedPreparedStatementCountUpdater.set(this, 0);
        preparedStatementCountUpdater.set(this, 0);
        transactionHistogram.reset();
        cachedPreparedStatementDeleteCountUpdater.set(this, 0);
        recycleErrorCountUpdater.set(this, 0);

        resetCountUpdater.incrementAndGet(this);
    }

    public long getResetCount() {
        return this.resetCount;
    }

    public boolean isEnable() {
        return enable;
    }

    public void setEnable(boolean enable) {
        lock.lock();
        try {
            this.enable = enable;
            if (!enable) {
                notEmpty.signalAll();
                notEmptySignalCount++;
            }
        } finally {
            lock.unlock();
        }
    }

    public void setPoolPreparedStatements(boolean value) {
        setPoolPreparedStatements0(value);
    }

    private void setPoolPreparedStatements0(boolean value) {
        if (this.poolPreparedStatements == value) {
            return;
        }

        this.poolPreparedStatements = value;

        if (!inited) {
            return;
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("set poolPreparedStatements " + this.poolPreparedStatements + " -> " + value);
        }

        if (!value) {
            lock.lock();
            try {

                for (int i = 0; i < poolingCount; ++i) {
                    DruidConnectionHolder connection = connections[i];

                    for (PreparedStatementHolder holder : connection.getStatementPool().getMap().values()) {
                        closePreapredStatement(holder);
                    }

                    connection.getStatementPool().getMap().clear();
                }
            } finally {
                lock.unlock();
            }
        }
    }

    public void setMaxActive(int maxActive) {
        if (this.maxActive == maxActive) {
            return;
        }

        if (maxActive == 0) {
            throw new IllegalArgumentException("maxActive can't not set zero");
        }

        if (!inited) {
            this.maxActive = maxActive;
            return;
        }

        if (maxActive < this.minIdle) {
            throw new IllegalArgumentException("maxActive less than minIdle, " + maxActive + " < " + this.minIdle);
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("maxActive changed : " + this.maxActive + " -> " + maxActive);
        }

        lock.lock();
        try {
            int allCount = this.poolingCount + this.activeCount;

            if (maxActive > allCount) {
                this.connections = Arrays.copyOf(this.connections, maxActive);
                evictConnections = new DruidConnectionHolder[maxActive];
                keepAliveConnections = new DruidConnectionHolder[maxActive];
            } else {
                this.connections = Arrays.copyOf(this.connections, allCount);
                evictConnections = new DruidConnectionHolder[allCount];
                keepAliveConnections = new DruidConnectionHolder[allCount];
            }

            this.maxActive = maxActive;
        } finally {
            lock.unlock();
        }
    }

    @SuppressWarnings("rawtypes")
    public void setConnectProperties(Properties properties) {
        if (properties == null) {
            properties = new Properties();
        }

        boolean equals;
        if (properties.size() == this.connectProperties.size()) {
            equals = true;
            for (Map.Entry entry : properties.entrySet()) {
                Object value = this.connectProperties.get(entry.getKey());
                Object entryValue = entry.getValue();
                if (value == null && entryValue != null) {
                    equals = false;
                    break;
                }

                if (!value.equals(entry.getValue())) {
                    equals = false;
                    break;
                }
            }
        } else {
            equals = false;
        }

        if (!equals) {
            if (inited && LOG.isInfoEnabled()) {
                LOG.info("connectProperties changed : " + this.connectProperties + " -> " + properties);
            }

            configFromPropety(properties);

            for (Filter filter : this.filters) {
                filter.configFromProperties(properties);
            }

            if (exceptionSorter != null) {
                exceptionSorter.configFromProperties(properties);
            }

            if (validConnectionChecker != null) {
                validConnectionChecker.configFromProperties(properties);
            }

            if (statLogger != null) {
                statLogger.configFromProperties(properties);
            }
        }

        this.connectProperties = properties;
    }

    public void init() throws SQLException {
        if (inited) {
            return; //如果已经被初始化过，则终止该方法
        }

        // bug fixed for dead lock, for issue #2980
        DruidDriver.getInstance();

        final ReentrantLock lock = this.lock;//获取重入锁
        try {
            lock.lockInterruptibly();//获取重入锁
        } catch (InterruptedException e) {
            throw new SQLException("interrupt", e);
        }

        boolean init = false;
        try {
            if (inited) {
                return;//双重检查
            }

            initStackTrace = Utils.toString(Thread.currentThread().getStackTrace());

            this.id = DruidDriver.createDataSourceId();//生成连接池id
            if (this.id > 1) {
                //生成其他对象的id，比如连接对象的id、statement对象的id
                long delta = (this.id - 1) * 100000;
                this.connectionIdSeedUpdater.addAndGet(this, delta);
                this.statementIdSeedUpdater.addAndGet(this, delta);
                this.resultSetIdSeedUpdater.addAndGet(this, delta);
                this.transactionIdSeedUpdater.addAndGet(this, delta);
            }

            if (this.jdbcUrl != null) {
                this.jdbcUrl = this.jdbcUrl.trim();
                //jdbc url的头必须是jdbc:wrap-jdbc才会触发该方法里的逻辑（这个头貌似是oracle的？仅针对mysql）
                initFromWrapDriverUrl();
            }

            for (Filter filter : filters) {
                //通过池对象初始化filters（因为filter里面可能会用到一些池属性）
                filter.init(this);
            }

            if (this.dbType == null || this.dbType.length() == 0) {
                //根据jdbc协议头分析出当前数据库的类型（本文默认mysql）
                this.dbType = JdbcUtils.getDbType(jdbcUrl, null);
            }

            if (JdbcConstants.MYSQL.equals(this.dbType)
                    || JdbcConstants.MARIADB.equals(this.dbType)
                    || JdbcConstants.OCEANBASE.equals(this.dbType)
                    || JdbcConstants.ALIYUN_ADS.equals(this.dbType)) {
                boolean cacheServerConfigurationSet = false;
                if (this.connectProperties.containsKey("cacheServerConfiguration")) {
                    cacheServerConfigurationSet = true;
                } else if (this.jdbcUrl.indexOf("cacheServerConfiguration") != -1) {
                    cacheServerConfigurationSet = true;
                }
                if (cacheServerConfigurationSet) {
                    this.connectProperties.put("cacheServerConfiguration", "true");
                }
            }

            //下面就是对设置的这些属性合理性的判断，不符合要求的将直接抛异常
            if (maxActive <= 0) {
                throw new IllegalArgumentException("illegal maxActive " + maxActive);
            }

            if (maxActive < minIdle) {
                throw new IllegalArgumentException("illegal maxActive " + maxActive);
            }

            if (getInitialSize() > maxActive) {
                throw new IllegalArgumentException("illegal initialSize " + this.initialSize + ", maxActive " + maxActive);
            }

            if (timeBetweenLogStatsMillis > 0 && useGlobalDataSourceStat) {
                throw new IllegalArgumentException("timeBetweenLogStatsMillis not support useGlobalDataSourceStat=true");
            }

            if (maxEvictableIdleTimeMillis < minEvictableIdleTimeMillis) {
                throw new SQLException("maxEvictableIdleTimeMillis must be grater than minEvictableIdleTimeMillis");
            }

            if (this.driverClass != null) {
                this.driverClass = driverClass.trim();
            }
            // 采用SPI机制加载过滤器，这部分过滤器除了放入filters，还会放入autoFilters
            // 通过SPI机制加载责任链上需要执行的filter，方法详情在下面
            initFromSPIServiceLoader();

            //如果driver为空，加载驱动，最终将加载到的驱动注册到DriverManager上去
            resolveDriver();

            //根据dbType的不同，来初始化一些标记字段（比如isMySql）
            initCheck();

            //异常处理器初始化
            initExceptionSorter();

            //初始化长连接检测时所需要用到的checker的适配类型，具体实现在下面
            initValidConnectionChecker();

            //简单的检测validationQuery参数是否填写了，若没填写会打印一个错误日志，不影响主流程
            validationQueryCheck();

            if (isUseGlobalDataSourceStat()) {//默认不开启，忽略
                dataSourceStat = JdbcDataSourceStat.getGlobal();
                if (dataSourceStat == null) {
                    dataSourceStat = new JdbcDataSourceStat("Global", "Global", this.dbType);
                    JdbcDataSourceStat.setGlobal(dataSourceStat);
                }
                if (dataSourceStat.getDbType() == null) {
                    dataSourceStat.setDbType(this.dbType);
                }
            } else {
                dataSourceStat = new JdbcDataSourceStat(this.name, this.jdbcUrl, this.dbType, this.connectProperties);
            }
            dataSourceStat.setResetStatEnable(this.resetStatEnable);

            //下面三个数组都跟池子本身有关系，所以容量为maxActive
            connections = new DruidConnectionHolder[maxActive];//初始化连接池本体
            evictConnections = new DruidConnectionHolder[maxActive];//初始化丢弃连接数组（流程4.1需要用到）
            keepAliveConnections = new DruidConnectionHolder[maxActive];//初始化需要检测可用性连接数组（流程4.1要用）


            SQLException connectError = null;

            if (createScheduler != null && asyncInit) {//另外一种通过线程池管理连接池的方式，默认不启用，忽略
                for (int i = 0; i < initialSize; ++i) {
                    submitCreateTask(true);
                }
            } else if (!asyncInit) {
                // init connections
                // 当池子里的连接数少于需要初始化的个数时，则需要不断新增连接填充连接池，直到等于初始化连接数
                while (poolingCount < initialSize) {
                    try {
                        //直接通过驱动程序创建连接对象，参考流程2.1
                        PhysicalConnectionInfo pyConnectInfo = createPhysicalConnection();

                        //拿着驱动连接包装成holder对象
                        DruidConnectionHolder holder = new DruidConnectionHolder(this, pyConnectInfo);

                        //生成好的连接直接往后排
                        connections[poolingCount++] = holder;

                    } catch (SQLException ex) {
                        LOG.error("init datasource error, url: " + this.getUrl(), ex);
                        if (initExceptionThrow) {
                            connectError = ex;
                            break;
                        } else {
                            Thread.sleep(3000);//异常报错后会休眠3s来进行下次的添加
                        }
                    }
                }

                if (poolingCount > 0) {
                    poolingPeak = poolingCount;
                    poolingPeakTime = System.currentTimeMillis();
                }
            }

            //开启打印log日志的守护线程
            createAndLogThread();

            //开启负责新增连接的守护线程（主流程3）
            createAndStartCreatorThread();

            //开启负责丢弃连接的守护线程（主流程4）
            createAndStartDestroyThread();

            //倒计数器，用来保证上面的主流程3和4两个守护线程全部开启完毕后才进行接下来的操作
            initedLatch.await();
            init = true;

            initedTime = new Date();
            registerMbean();

            if (connectError != null && poolingCount == 0) {
                throw connectError;
            }

            if (keepAlive) {
                // async fill to minIdle
                if (createScheduler != null) {//默认不启用该模式，忽略
                    for (int i = 0; i < minIdle; ++i) {
                        submitCreateTask(true);
                    }
                } else {
                    this.emptySignal();//keepAlive=true，主动唤起主流程3一次
                }
            }

        } catch (SQLException e) {
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;
        } catch (InterruptedException e) {
            throw new SQLException(e.getMessage(), e);
        } catch (RuntimeException e){
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;
        } catch (Error e){
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;

        } finally {
            inited = true;//初始化完成后置为true
            lock.unlock();//释放锁

            if (init && LOG.isInfoEnabled()) {
                String msg = "{dataSource-" + this.getID();

                if (this.name != null && !this.name.isEmpty()) {
                    msg += ",";
                    msg += this.name;
                }

                msg += "} inited";

                LOG.info(msg);
            }
        }
    }

    private void submitCreateTask(boolean initTask) {
        createTaskCount++;
        CreateConnectionTask task = new CreateConnectionTask(initTask);
        if (createTasks == null) {
            createTasks = new long[8];
        }

        boolean putted = false;
        for (int i = 0; i < createTasks.length; ++i) {
            if (createTasks[i] == 0) {
                createTasks[i] = task.taskId;
                putted = true;
                break;
            }
        }
        if (!putted) {
            long[] array = new long[createTasks.length * 3 / 2];
            System.arraycopy(createTasks, 0, array, 0, createTasks.length);
            array[createTasks.length] = task.taskId;
            createTasks = array;
        }

        this.createSchedulerFuture = createScheduler.submit(task);
    }

    private boolean clearCreateTask(long taskId) {
        if (createTasks == null) {
            return false;
        }

        if (taskId == 0) {
            return false;
        }

        for (int i = 0; i < createTasks.length; i++) {
            if (createTasks[i] == taskId) {
                createTasks[i] = 0;
                createTaskCount--;

                if (createTaskCount < 0) {
                    createTaskCount = 0;
                }

                if (createTaskCount == 0 && createTasks.length > 8) {
                    createTasks = new long[8];
                }
                return true;
            }
        }

        if (LOG.isWarnEnabled()) {
            LOG.warn("clear create task failed : " + taskId);
        }

        return false;
    }

    private void createAndLogThread() {
        if (this.timeBetweenLogStatsMillis <= 0) {
            return;
        }

        String threadName = "Druid-ConnectionPool-Log-" + System.identityHashCode(this);
        logStatsThread = new LogStatsThread(threadName);
        logStatsThread.start();

        this.resetStatEnable = false;
    }

    protected void createAndStartDestroyThread() {
        destroyTask = new DestroyTask();

        if (destroyScheduler != null) {
            long period = timeBetweenEvictionRunsMillis;
            if (period <= 0) {
                period = 1000;
            }
            destroySchedulerFuture = destroyScheduler.scheduleAtFixedRate(destroyTask, period, period,
                                                                          TimeUnit.MILLISECONDS);
            initedLatch.countDown();
            return;
        }

        String threadName = "Druid-ConnectionPool-Destroy-" + System.identityHashCode(this);
        destroyConnectionThread = new DestroyConnectionThread(threadName);
        destroyConnectionThread.start();
    }

    protected void createAndStartCreatorThread() {
        if (createScheduler == null) {
            String threadName = "Druid-ConnectionPool-Create-" + System.identityHashCode(this);
            createConnectionThread = new CreateConnectionThread(threadName);
            createConnectionThread.start();
            return;
        }

        initedLatch.countDown();
    }

    /**
     * load filters from SPI ServiceLoader
     * 采用SPI机制加载过滤器，这部分过滤器除了放入filters，还会放入autoFilters
     * @see ServiceLoader
     */
    private void initFromSPIServiceLoader() {
        if (loadSpifilterSkip) {//默认不跳过SPI加载
            return;
        }

        if (autoFilters == null) {
            List<Filter> filters = new ArrayList<Filter>();
            ServiceLoader<Filter> autoFilterLoader = ServiceLoader.load(Filter.class);//加载Filter的实现

            for (Filter filter : autoFilterLoader) {
                AutoLoad autoLoad = filter.getClass().getAnnotation(AutoLoad.class);
                if (autoLoad != null && autoLoad.value()) {
                    filters.add(filter);
                }
            }
            autoFilters = filters;
        }

        for (Filter filter : autoFilters) {
            if (LOG.isInfoEnabled()) {
                LOG.info("load filter from spi :" + filter.getClass().getName());
            }
            addFilter(filter); //把通过SPI机制加载到的filter放到池子的filters里，用于后续责任链触发
        }
    }

    /**
     * 针对druid自定义的一种url格式，进行解析
     * jdbc:wrap-jdbc:开头，可设置driver、name、jmx等
     * @throws SQLException
     */
    private void initFromWrapDriverUrl() throws SQLException {
        if (!jdbcUrl.startsWith(DruidDriver.DEFAULT_PREFIX)) {
            return;
        }

        DataSourceProxyConfig config = DruidDriver.parseConfig(jdbcUrl, null);
        this.driverClass = config.getRawDriverClassName();

        LOG.error("error url : '" + jdbcUrl + "', it should be : '" + config.getRawUrl() + "'");

        this.jdbcUrl = config.getRawUrl();
        if (this.name == null) {
            this.name = config.getName();
        }

        for (Filter filter : config.getFilters()) {
            //去重
            addFilter(filter);
        }
    }

    /**
     * 会去重复
     * 
     * @param filter
     */
    private void addFilter(Filter filter) {
        boolean exists = false;
        for (Filter initedFilter : this.filters) {
            if (initedFilter.getClass() == filter.getClass()) {
                exists = true;
                break;
            }
        }

        if (!exists) {
            filter.init(this);
            this.filters.add(filter);
        }

    }

    private void validationQueryCheck() {
        if (!(testOnBorrow || testOnReturn || testWhileIdle)) {
            return;
        }

        if (this.validConnectionChecker != null) {
            return;
        }

        if (this.validationQuery != null && this.validationQuery.length() > 0) {
            return;
        }

        String errorMessage = "";

        if (testOnBorrow) {
            errorMessage += "testOnBorrow is true, ";
        }

        if (testOnReturn) {
            errorMessage += "testOnReturn is true, ";
        }

        if (testWhileIdle) {
            errorMessage += "testWhileIdle is true, ";
        }

        LOG.error(errorMessage + "validationQuery not set");
    }

    //如果driver为空，加载驱动，最终将加载到的驱动注册到DriverManager上去
    protected void resolveDriver() throws SQLException {
        if (this.driver == null) {
            if (this.driverClass == null || this.driverClass.isEmpty()) {
                //在driverClass不配置的情况下，druid会通过url来判定属于哪个driverClass
                this.driverClass = JdbcUtils.getDriverClassName(this.jdbcUrl);
            }

            if (MockDriver.class.getName().equals(driverClass)) {
                driver = MockDriver.instance;
            } else {
                if (jdbcUrl == null && (driverClass == null || driverClass.length() == 0)) {
                    throw new SQLException("url not set");
                }
                //driverClass不为空的情况下直接触发驱动加载
                driver = JdbcUtils.createDriver(driverClassLoader, driverClass);
            }
        } else {//除非手动设置驱动，否则不会走这里的逻辑
            if (this.driverClass == null) {
                this.driverClass = driver.getClass().getName();
            }
        }
    }

    //根据dbType的不同，来初始化一些标记字段（比如isMySql）
    protected void initCheck() throws SQLException {
        if (JdbcUtils.ORACLE.equals(this.dbType)) {
            isOracle = true;

            if (driver.getMajorVersion() < 10) {
                throw new SQLException("not support oracle driver " + driver.getMajorVersion() + "."
                                       + driver.getMinorVersion());
            }

            if (driver.getMajorVersion() == 10 && isUseOracleImplicitCache()) {
                this.getConnectProperties().setProperty("oracle.jdbc.FreeMemoryOnEnterImplicitCache", "true");
            }

            oracleValidationQueryCheck();
        } else if (JdbcUtils.DB2.equals(dbType)) {
            db2ValidationQueryCheck();
        } else if (JdbcUtils.MYSQL.equals(this.dbType)
                || JdbcUtils.MYSQL_DRIVER_6.equals(this.dbType)) {
            isMySql = true;
        }

        if (removeAbandoned) {
            LOG.warn("removeAbandoned is true, not use in production.");
        }
    }

    private void oracleValidationQueryCheck() {
        if (validationQuery == null) {
            return;
        }
        if (validationQuery.length() == 0) {
            return;
        }

        SQLStatementParser sqlStmtParser = SQLParserUtils.createSQLStatementParser(validationQuery, this.dbType);
        List<SQLStatement> stmtList = sqlStmtParser.parseStatementList();

        if (stmtList.size() != 1) {
            return;
        }

        SQLStatement stmt = stmtList.get(0);
        if (!(stmt instanceof SQLSelectStatement)) {
            return;
        }

        SQLSelectQuery query = ((SQLSelectStatement) stmt).getSelect().getQuery();
        if (query instanceof SQLSelectQueryBlock) {
            if (((SQLSelectQueryBlock) query).getFrom() == null) {
                LOG.error("invalid oracle validationQuery. " + validationQuery + ", may should be : " + validationQuery
                          + " FROM DUAL");
            }
        }
    }

    private void db2ValidationQueryCheck() {
        if (validationQuery == null) {
            return;
        }
        if (validationQuery.length() == 0) {
            return;
        }

        SQLStatementParser sqlStmtParser = SQLParserUtils.createSQLStatementParser(validationQuery, this.dbType);
        List<SQLStatement> stmtList = sqlStmtParser.parseStatementList();

        if (stmtList.size() != 1) {
            return;
        }

        SQLStatement stmt = stmtList.get(0);
        if (!(stmt instanceof SQLSelectStatement)) {
            return;
        }

        SQLSelectQuery query = ((SQLSelectStatement) stmt).getSelect().getQuery();
        if (query instanceof SQLSelectQueryBlock) {
            if (((SQLSelectQueryBlock) query).getFrom() == null) {
                LOG.error("invalid db2 validationQuery. " + validationQuery + ", may should be : " + validationQuery
                          + " FROM SYSDUMMY");
            }
        }
    }

    private void initValidConnectionChecker() {//初始化checker
        if (this.validConnectionChecker != null) {
            return;
        }

        String realDriverClassName = driver.getClass().getName();//根据驱动的class名称，来适配具体的checker实现
        if (JdbcUtils.isMySqlDriver(realDriverClassName)) {
            //假设是mysql类型的驱动，那么适配到mysql的checker，MySqlValidConnectionChecker的构造器参考下面的方法
            this.validConnectionChecker = new MySqlValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER)
                || realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER2)) {
            this.validConnectionChecker = new OracleValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.SQL_SERVER_DRIVER)
                   || realDriverClassName.equals(JdbcConstants.SQL_SERVER_DRIVER_SQLJDBC4)
                   || realDriverClassName.equals(JdbcConstants.SQL_SERVER_DRIVER_JTDS)) {
            this.validConnectionChecker = new MSSQLValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.POSTGRESQL_DRIVER)
                || realDriverClassName.equals(JdbcConstants.ENTERPRISEDB_DRIVER)
                || realDriverClassName.equals(JdbcConstants.POLARDB_DRIVER)) {
            this.validConnectionChecker = new PGValidConnectionChecker();
        }
    }

    private void initExceptionSorter() {
        if (exceptionSorter instanceof NullExceptionSorter) {
            if (driver instanceof MockDriver) {
                return;
            }
        } else if (this.exceptionSorter != null) {
            return;
        }


        for (Class<?> driverClass = driver.getClass();;) {
            String realDriverClassName = driverClass.getName();
            if (realDriverClassName.equals(JdbcConstants.MYSQL_DRIVER) //
                    || realDriverClassName.equals(JdbcConstants.MYSQL_DRIVER_6)) {
                this.exceptionSorter = new MySqlExceptionSorter();
                this.isMySql = true;
            } else if (realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER)
                    || realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER2)) {
                this.exceptionSorter = new OracleExceptionSorter();
            } else if (realDriverClassName.equals(JdbcConstants.OCEANBASE_DRIVER)) { // 写一个真实的 TestCase
                if (JdbcUtils.OCEANBASE_ORACLE.equalsIgnoreCase(dbType)) {
                    this.exceptionSorter = new OceanBaseOracleExceptionSorter();
                } else {
                    this.exceptionSorter = new MySqlExceptionSorter();
                }
            } else if (realDriverClassName.equals("com.informix.jdbc.IfxDriver")) {
                this.exceptionSorter = new InformixExceptionSorter();

            } else if (realDriverClassName.equals("com.sybase.jdbc2.jdbc.SybDriver")) {
                this.exceptionSorter = new SybaseExceptionSorter();

            } else if (realDriverClassName.equals(JdbcConstants.POSTGRESQL_DRIVER)
                    || realDriverClassName.equals(JdbcConstants.ENTERPRISEDB_DRIVER)
                    || realDriverClassName.equals(JdbcConstants.POLARDB_DRIVER)) {
                this.exceptionSorter = new PGExceptionSorter();

            } else if (realDriverClassName.equals("com.alibaba.druid.mock.MockDriver")) {
                this.exceptionSorter = new MockExceptionSorter();
            } else if (realDriverClassName.contains("DB2")) {
                this.exceptionSorter = new DB2ExceptionSorter();

            } else {
                Class<?> superClass = driverClass.getSuperclass();
                if (superClass != null && superClass != Object.class) {
                    driverClass = superClass;
                    continue;
                }
            }

            break;
        }
    }

    @Override
    public DruidPooledConnection getConnection() throws SQLException {
        return getConnection(maxWait);
    }

    public DruidPooledConnection getConnection(long maxWaitMillis) throws SQLException {
        init();//初始化

        if (filters.size() > 0) { //责任链上的filter存在
            // 责任链，内部也是触发下面的getConnectionDirect方法，只是要走一遍责任链上每个filter的逻辑，这里不做描述，
            // 后续放到流程1.1里体现
            FilterChainImpl filterChain = new FilterChainImpl(this);//该类是执行整个责任链的执行者

            //每个需要执行责任链的方法，在filterChain里都可以找到映射方法，比如本方法getConnection，
            //就对应filterChain.dataSource_connect（参考流程1.1）
            return filterChain.dataSource_connect(this, maxWaitMillis);
        } else {
            return getConnectionDirect(maxWaitMillis);//触发getConnectionDirect
        }
    }

    @Override
    public PooledConnection getPooledConnection() throws SQLException {
        return getConnection(maxWait);
    }

    @Override
    public PooledConnection getPooledConnection(String user, String password) throws SQLException {
        throw new UnsupportedOperationException("Not supported by DruidDataSource");
    }

    public DruidPooledConnection getConnectionDirect(long maxWaitMillis) throws SQLException {
        int notFullTimeoutRetryCnt = 0;
        for (;;) {//死循环
            // handle notFullTimeoutRetry
            /**
             * 真正返回出去的连接对象，注意这里是被druid包装成了DruidPooledConnection类型，
             * 实际上池子里存放的连接类型是DruidConnectionHolder，DruidPooledConnection类本身持有一个holder属性，
             * 用于保存真正的连接对象，而DruidConnectionHolder才是真正保存驱动连接对象的类。
             */
            DruidPooledConnection poolableConnection;
            try {
                //从池子里获取连接，这一个后续放到流程1.2体现
                poolableConnection = getConnectionInternal(maxWaitMillis);
            } catch (GetConnectionTimeoutException ex) {
                // 出现了超时异常，在连接池没满且重试次数未超过上限的情况下，重试一次
                // （notFullTimeoutRetryCount默认是0，所以至少可以重试一次）。
                if (notFullTimeoutRetryCnt <= this.notFullTimeoutRetryCount && !isFull()) {
                    //重试次数+1
                    notFullTimeoutRetryCnt++;
                    if (LOG.isWarnEnabled()) {
                        LOG.warn("get connection timeout retry : " + notFullTimeoutRetryCnt);
                    }
                    continue;
                }
                throw ex;//超过重试次数或者池子已满仍然获取失败，则直接抛出异常
            }

            if (testOnBorrow) {//testOnBorrow开启时，每次都进行检测连接可用性
                boolean validate = testConnectionInternal(poolableConnection.holder, poolableConnection.conn);
                if (!validate) {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("skip not validate connection.");
                    }
                    //若连接不可用，则触发discard，这个方法具体放到流程1.4体现
                    discardConnection(poolableConnection.holder);
                    continue;
                }
            } else {
                if (poolableConnection.conn.isClosed()) {
                    discardConnection(poolableConnection.holder); // 传入null，避免重复关闭
                    continue;
                }
                //不启用testOnBorrow的情况下，才会判断是否启用testWhileIdle
                if (testWhileIdle) {
                    final DruidConnectionHolder holder = poolableConnection.holder;
                    long currentTimeMillis             = System.currentTimeMillis();
                    long lastActiveTimeMillis          = holder.lastActiveTimeMillis;
                    long lastExecTimeMillis            = holder.lastExecTimeMillis;//上次被使用的时间
                    long lastKeepTimeMillis            = holder.lastKeepTimeMillis;

                    if (checkExecuteTime
                            && lastExecTimeMillis != lastActiveTimeMillis) {
                        lastActiveTimeMillis = lastExecTimeMillis;
                    }

                    if (lastKeepTimeMillis > lastActiveTimeMillis) {
                        lastActiveTimeMillis = lastKeepTimeMillis;
                    }
                    //计算出闲置时间
                    long idleMillis                    = currentTimeMillis - lastActiveTimeMillis;

                    long timeBetweenEvictionRunsMillis = this.timeBetweenEvictionRunsMillis;

                    if (timeBetweenEvictionRunsMillis <= 0) {
                        timeBetweenEvictionRunsMillis = DEFAULT_TIME_BETWEEN_EVICTION_RUNS_MILLIS;
                    }
                    //当闲置时间超出timeBetweenEvictionRunsMillis（默认60s）时，则触发检查逻辑
                    if (idleMillis >= timeBetweenEvictionRunsMillis
                            || idleMillis < 0 // unexcepted branch
                            ) {
                        boolean validate = testConnectionInternal(poolableConnection.holder, poolableConnection.conn);
                        if (!validate) {
                            if (LOG.isDebugEnabled()) {
                                LOG.debug("skip not validate connection.");
                            }
                            //连接不可用，同样触发discard
                            discardConnection(poolableConnection.holder);
                             continue;
                        }
                    }
                }
            }
            //若开启removeAbandoned，则把当前拿到的连接放到activeConnections里，方便后续检查（后面流程4.2体现）
            if (removeAbandoned) {
                StackTraceElement[] stackTrace = Thread.currentThread().getStackTrace();
                poolableConnection.connectStackTrace = stackTrace;
                //设置连接获取时间为当前时间
                poolableConnection.setConnectedTimeNano();
                //这个设置为true，则在归还该连接时会在activeConnections里清除掉该连接对象
                poolableConnection.traceEnable = true;

                activeConnectionLock.lock();
                try {
                    activeConnections.put(poolableConnection, PRESENT);
                } finally {
                    activeConnectionLock.unlock();
                }
            }
            //默认是不开事务的，所以这里是true，不会触发下面的逻辑；这个不建议手动设置默认值，
            // 一般开启事务的工作自己做或者交给第三方框架（如spring）做比较好
            if (!this.defaultAutoCommit) {
                poolableConnection.setAutoCommit(false);
            }
            //最终返回可用连接
            return poolableConnection;
        }
    }

    /**
     * 抛弃连接，不进行回收，而是抛弃
     * 
     * @param realConnection
     * @deprecated
     */
    public void discardConnection(Connection realConnection) {
        JdbcUtils.close(realConnection);

        lock.lock();
        try {
            activeCount--;
            discardCount++;

            if (activeCount <= minIdle) {
                emptySignal();
            }
        } finally {
            lock.unlock();
        }
    }
    //丢弃连接
    public void discardConnection(DruidConnectionHolder holder) {
        if (holder == null) {
            return;
        }

        Connection conn = holder.getConnection();
        if (conn != null) {
            //close掉真正的连接对象，一般调用该方法传入的connection对象都是最原始的驱动连接对象，所以这里并不会触发recycle
            JdbcUtils.close(conn);
        }

        lock.lock();
        try {
            if (holder.discard) {
                return;
            }

            if (holder.active) {
                activeCount--; //活跃连接数-1
                holder.active = false;
            }
            discardCount++;//丢弃连接数+1

            holder.discard = true;

            if (activeCount <= minIdle) {
                emptySignal();//唤起一次主流程3新增连接
            }
        } finally {
            lock.unlock();
        }
    }

    private DruidPooledConnection getConnectionInternal(long maxWait) throws SQLException {
        //可用性判断
        if (closed) {
            connectErrorCountUpdater.incrementAndGet(this);
            throw new DataSourceClosedException("dataSource already closed at " + new Date(closeTimeMillis));
        }

        if (!enable) {
            connectErrorCountUpdater.incrementAndGet(this);

            if (disableException != null) {
                throw disableException;
            }

            throw new DataSourceDisableException();
        }

        final long nanos = TimeUnit.MILLISECONDS.toNanos(maxWait);//纳秒
        final int maxWaitThreadCount = this.maxWaitThreadCount;//目前因为拿不到连接而发生阻塞的业务线程数

        DruidConnectionHolder holder;

        for (boolean createDirect = false;;) {
            if (createDirect) {//模式未启用，恒等false，下面的逻辑不会触发
                createStartNanosUpdater.set(this, System.nanoTime());
                if (creatingCountUpdater.compareAndSet(this, 0, 1)) {
                    PhysicalConnectionInfo pyConnInfo = DruidDataSource.this.createPhysicalConnection();
                    holder = new DruidConnectionHolder(this, pyConnInfo);
                    holder.lastActiveTimeMillis = System.currentTimeMillis();

                    creatingCountUpdater.decrementAndGet(this);
                    directCreateCountUpdater.incrementAndGet(this);

                    if (LOG.isDebugEnabled()) {
                        LOG.debug("conn-direct_create ");
                    }

                    boolean discard = false;
                    lock.lock(); //锁获取
                    try {
                        if (activeCount < maxActive) {
                            activeCount++;
                            holder.active = true;
                            if (activeCount > activePeak) {
                                activePeak = activeCount;
                                activePeakTime = System.currentTimeMillis();
                            }
                            break;
                        } else {
                            discard = true;
                        }
                    } finally {
                        lock.unlock();
                    }

                    if (discard) {
                        JdbcUtils.close(pyConnInfo.getPhysicalConnection());
                    }
                }
            }

            try {
                lock.lockInterruptibly(); //锁获取
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            try {
                //如果因为拿不到连接而阻塞的业务线程数达到阈值，则直接抛异常
                if (maxWaitThreadCount > 0
                        && notEmptyWaitThreadCount >= maxWaitThreadCount) {
                    connectErrorCountUpdater.incrementAndGet(this);
                    throw new SQLException("maxWaitThreadCount " + maxWaitThreadCount + ", current wait Thread count "
                            + lock.getQueueLength());
                }

                if (onFatalError
                        && onFatalErrorMaxActive > 0
                        && activeCount >= onFatalErrorMaxActive) {
                    connectErrorCountUpdater.incrementAndGet(this);

                    StringBuilder errorMsg = new StringBuilder();
                    errorMsg.append("onFatalError, activeCount ")
                            .append(activeCount)
                            .append(", onFatalErrorMaxActive ")
                            .append(onFatalErrorMaxActive);

                    if (lastFatalErrorTimeMillis > 0) {
                        errorMsg.append(", time '")
                                .append(StringUtils.formatDateTime19(
                                        lastFatalErrorTimeMillis, TimeZone.getDefault()))
                                .append("'");
                    }

                    if (lastFatalErrorSql != null) {
                        errorMsg.append(", sql \n")
                                .append(lastFatalErrorSql);
                    }

                    throw new SQLException(
                            errorMsg.toString(), lastFatalError);
                }

                connectCount++;//连接数累加

                if (createScheduler != null
                        && poolingCount == 0
                        && activeCount < maxActive
                        && creatingCountUpdater.get(this) == 0
                        && createScheduler instanceof ScheduledThreadPoolExecutor) {
                    ScheduledThreadPoolExecutor executor = (ScheduledThreadPoolExecutor) createScheduler;
                    if (executor.getQueue().size() > 0) {
                        //createScheduler这种异步添加模式不开启（默认不开启，本文也不是基于该模式的），
                        // createDirect永远不等于true，所以上面createDirect==true的代码不会被触发
                        createDirect = true;
                        continue;
                    }
                }

                if (maxWait > 0) {
                    holder = pollLast(nanos);//尝试从池子里获取连接
                } else {
                    holder = takeLast();
                }

                if (holder != null) {
                    if (holder.discard) {
                        continue;
                    }

                    //拿到连接，activeCount累加
                    activeCount++;
                    holder.active = true;
                    if (activeCount > activePeak) {
                        activePeak = activeCount;
                        activePeakTime = System.currentTimeMillis();
                    }
                }
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException(e.getMessage(), e);
            } catch (SQLException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw e;
            } finally {
                lock.unlock();
            }

            break;
        }

        if (holder == null) { //没有获取到连接，整理错误信息，抛出错误
            long waitNanos = waitNanosLocal.get();

            StringBuilder buf = new StringBuilder(128);
            buf.append("wait millis ")//
               .append(waitNanos / (1000 * 1000))//
               .append(", active ").append(activeCount)//
               .append(", maxActive ").append(maxActive)//
               .append(", creating ").append(creatingCount)//
            ;
            if (creatingCount > 0 && createStartNanos > 0) {
                long createElapseMillis = (System.nanoTime() - createStartNanos) / (1000 * 1000);
                if (createElapseMillis > 0) {
                    buf.append(", createElapseMillis ").append(createElapseMillis);
                }
            }

            if (createErrorCount > 0) {
                buf.append(", createErrorCount ").append(createErrorCount);
            }

            List<JdbcSqlStatValue> sqlList = this.getDataSourceStat().getRuningSqlList();
            for (int i = 0; i < sqlList.size(); ++i) {
                if (i != 0) {
                    buf.append('\n');
                } else {
                    buf.append(", ");
                }
                JdbcSqlStatValue sql = sqlList.get(i);
                buf.append("runningSqlCount ").append(sql.getRunningCount());
                buf.append(" : ");
                buf.append(sql.getSql());
            }

            String errorMessage = buf.toString();

            if (this.createError != null) {
                throw new GetConnectionTimeoutException(errorMessage, createError);
            } else {
                throw new GetConnectionTimeoutException(errorMessage);
            }
        }

        holder.incrementUseCount();

        DruidPooledConnection poolalbeConnection = new DruidPooledConnection(holder);//包装成目标对象
        return poolalbeConnection;//返回
    }

    public void handleConnectionException(DruidPooledConnection pooledConnection, Throwable t, String sql) throws SQLException {
        final DruidConnectionHolder holder = pooledConnection.getConnectionHolder();
        if (holder == null) {
            return;
        }

        errorCountUpdater.incrementAndGet(this);
        lastError = t;
        lastErrorTimeMillis = System.currentTimeMillis();

        if (t instanceof SQLException) {
            SQLException sqlEx = (SQLException) t;

            // broadcastConnectionError
            ConnectionEvent event = new ConnectionEvent(pooledConnection, sqlEx);
            for (ConnectionEventListener eventListener : holder.getConnectionEventListeners()) {
                eventListener.connectionErrorOccurred(event);
            }

            // exceptionSorter.isExceptionFatal
            if (exceptionSorter != null && exceptionSorter.isExceptionFatal(sqlEx)) {
                handleFatalError(pooledConnection, sqlEx, sql);
            }

            throw sqlEx;
        } else {
            throw new SQLException("Error", t);
        }
    }

    protected final void handleFatalError(DruidPooledConnection conn, SQLException error, String sql) throws SQLException {
        final DruidConnectionHolder holder = conn.holder;

        if (conn.isTraceEnable()) {
            activeConnectionLock.lock();
            try {
                if (conn.isTraceEnable()) {
                    activeConnections.remove(conn);
                    conn.setTraceEnable(false);
                }
            } finally {
                activeConnectionLock.unlock();
            }
        }

        long lastErrorTimeMillis = this.lastErrorTimeMillis;
        if (lastErrorTimeMillis == 0) {
            lastErrorTimeMillis = System.currentTimeMillis();
        }

        if (sql != null && sql.length() > 1024) {
            sql = sql.substring(0, 1024);
        }

        boolean requireDiscard = false;
        final ReentrantLock lock = conn.lock;
        lock.lock();
        try {
            if ((!conn.isClosed()) || !conn.isDisable()) {
                conn.disable(error);
                requireDiscard = true;
            }

            lastFatalErrorTimeMillis = lastErrorTimeMillis;
            fatalErrorCount++;
            if (fatalErrorCount - fatalErrorCountLastShrink > onFatalErrorMaxActive) {
                onFatalError = true;
            }
            lastFatalError = error;
            lastFatalErrorSql = sql;
        } finally {
            lock.unlock();
        }

        if(onFatalError && holder != null && holder.getDataSource() != null) {
            ReentrantLock dataSourceLock = holder.getDataSource().lock;
            dataSourceLock.lock();
            try {
                emptySignal();
            }
            finally {
                dataSourceLock.unlock();
            }
        }

        if (requireDiscard) {
            if (holder.statementTrace != null) {
                holder.lock.lock();
                try {
                    for (Statement stmt : holder.statementTrace) {
                        JdbcUtils.close(stmt);
                    }
                } finally {
                    holder.lock.unlock();
                }
            }

            this.discardConnection(holder);
        }

        LOG.error("discard connection", error);
    }

    /**
     * 回收连接
     */
    //DruidDataSource类里的recycle方法，真正回收连接的方法，由上面DruidPooledConnection类的recycle触发
    protected void recycle(DruidPooledConnection pooledConnection) throws SQLException {
        final DruidConnectionHolder holder = pooledConnection.holder;

        if (holder == null) {
            LOG.warn("connectionHolder is null");
            return;
        }

        if (logDifferentThread //
            && (!isAsyncCloseConnectionEnable()) //
            && pooledConnection.ownerThread != Thread.currentThread()//
        ) {
            LOG.warn("get/close not same thread");
        }

        final Connection physicalConnection = holder.conn;//拿到真正的驱动连接对象
        //如果traceEnable为true（满足该属性为true，必须要removeAbandoned设置为true，这样在主流程1那里才会被放进activeConnections，才会置为true），
        // 流程4.2处理过后，会把该属性重新置为false，其他情况均为true
        if (pooledConnection.traceEnable) {
            Object oldInfo = null;
            activeConnectionLock.lock();
            try {
                if (pooledConnection.traceEnable) {//双重检查
                    oldInfo = activeConnections.remove(pooledConnection);//从activeConnections移除，防止流程4.2的重复检查
                    pooledConnection.traceEnable = false; //置为false
                }
            } finally {
                activeConnectionLock.unlock();
            }
            if (oldInfo == null) {
                if (LOG.isWarnEnabled()) {
                    LOG.warn("remove abandonded failed. activeConnections.size " + activeConnections.size());
                }
            }
        }

        final boolean isAutoCommit = holder.underlyingAutoCommit;
        final boolean isReadOnly = holder.underlyingReadOnly;
        final boolean testOnReturn = this.testOnReturn;

        try {
            // check need to rollback?
            // 如果在归还至连接池时发现此连接对象还有未处理完的事务，则直接回滚
            if ((!isAutoCommit) && (!isReadOnly)) {
                pooledConnection.rollback();
            }

            // reset holder, restore default settings, clear warnings
            boolean isSameThread = pooledConnection.ownerThread == Thread.currentThread();
            if (!isSameThread) {//同样判断线程，为了保证安全性
                final ReentrantLock lock = pooledConnection.lock;
                lock.lock();
                try {
                    //连接被借出去后，可能被业务方改动了一些属性（典型的比如autoCommit），现在利用reset方法还原为默认值
                    holder.reset();
                } finally {
                    lock.unlock();
                }
            } else {
                //同上，这里认为获取和关闭连接的是同一个线程，不存在线程安全问题，因此不用去竞争锁
                holder.reset();
            }
            //连接已被抛弃，则不作任何处理（不再归还）
            if (holder.discard) {
                return;
            }
            //忽略
            if (phyMaxUseCount > 0 && holder.useCount >= phyMaxUseCount) {
                discardConnection(holder);
                return;
            }
            //如果驱动连接本身被人为关闭了，除一些监控值之外，也不做处理
            if (physicalConnection.isClosed()) {
                lock.lock();
                try {
                    if (holder.active) {
                        activeCount--;
                        holder.active = false;
                    }
                    closeCount++;
                } finally {
                    lock.unlock();
                }
                return;
            }
            //参考testOnBorrow，这里testOnReturn就是指每次回收连接都要做连接可用性检查，同样官方不建议开启，影响性能，缺省值也是不开启的

            if (testOnReturn) {
                boolean validate = testConnectionInternal(holder, physicalConnection);
                if (!validate) {
                    JdbcUtils.close(physicalConnection);

                    destroyCountUpdater.incrementAndGet(this);

                    lock.lock();
                    try {
                        if (holder.active) {
                            activeCount--;
                            holder.active = false;
                        }
                        closeCount++;
                    } finally {
                        lock.unlock();
                    }
                    return;
                }
            }

            if (!enable) {
                //中途发现连接又被置为不可用，则直接触发抛弃方法，参考流程1.4和代码段1-5
                discardConnection(holder);
                return;
            }

            boolean result;
            final long currentTimeMillis = System.currentTimeMillis();

            if (phyTimeoutMillis > 0) {
                long phyConnectTimeMillis = currentTimeMillis - holder.connectTimeMillis;
                if (phyConnectTimeMillis > phyTimeoutMillis) {
                    discardConnection(holder);
                    return;
                }
            }

            lock.lock();
            try {
                if (holder.active) {
                    activeCount--;
                    holder.active = false;
                }
                closeCount++;
                //最终放入池子，方法详情在下方
                result = putLast(holder, currentTimeMillis);
                recycleCount++;
            } finally {
                lock.unlock();
            }
            //如果加不进去，则直接关闭驱动连接，然后不处理（此时holder已经失去强引用，不久便会被回收）
            if (!result) {
                JdbcUtils.close(holder.conn);
                LOG.info("connection recyle failed.");
            }
        } catch (Throwable e) {
            holder.clearStatementCache();

            if (!holder.discard) {
                discardConnection(holder);
                holder.discard = true;
            }

            LOG.error("recyle error", e);
            recycleErrorCountUpdater.incrementAndGet(this);
        }
    }

    public long getRecycleErrorCount() {
        return recycleErrorCount;
    }

    public void clearStatementCache() throws SQLException {
        lock.lock();
        try {
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder conn = connections[i];

                if (conn.statementPool != null) {
                    conn.statementPool.clear();
                }
            }
        } finally {
            lock.unlock();
        }
    }

    /**
     * close datasource
     */
    public void close() {
        if (LOG.isInfoEnabled()) {
            LOG.info("{dataSource-" + this.getID() + "} closing ...");
        }

        lock.lock();
        try {
            if (this.closed) {
                return;
            }

            if (!this.inited) {
                return;
            }

            this.closing = true;

            if (logStatsThread != null) {
                logStatsThread.interrupt();
            }

            if (createConnectionThread != null) {
                createConnectionThread.interrupt();
            }

            if (destroyConnectionThread != null) {
                destroyConnectionThread.interrupt();
            }

            if (createSchedulerFuture != null) {
                createSchedulerFuture.cancel(true);
            }

            if (destroySchedulerFuture != null) {
                destroySchedulerFuture.cancel(true);
            }

            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder connHolder = connections[i];

                for (PreparedStatementHolder stmtHolder : connHolder.getStatementPool().getMap().values()) {
                    connHolder.getStatementPool().closeRemovedStatement(stmtHolder);
                }
                connHolder.getStatementPool().getMap().clear();

                Connection physicalConnection = connHolder.getConnection();
                try {
                    physicalConnection.close();
                } catch (Exception ex) {
                    LOG.warn("close connection error", ex);
                }
                connections[i] = null;
                destroyCountUpdater.incrementAndGet(this);
            }
            poolingCount = 0;
            unregisterMbean();

            enable = false;
            notEmpty.signalAll();
            notEmptySignalCount++;

            this.closed = true;
            this.closeTimeMillis = System.currentTimeMillis();

            disableException = new DataSourceDisableException();

            for (Filter filter : filters) {
                filter.destroy();
            }
        } finally {
            lock.unlock();
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("{dataSource-" + this.getID() + "} closed");
        }
    }

    public void registerMbean() {
        if (!mbeanRegistered) {
            AccessController.doPrivileged(new PrivilegedAction<Object>() {

                @Override
                public Object run() {
                    ObjectName objectName = DruidDataSourceStatManager.addDataSource(DruidDataSource.this,
                                                                                     DruidDataSource.this.name);

                    DruidDataSource.this.setObjectName(objectName);
                    DruidDataSource.this.mbeanRegistered = true;

                    return null;
                }
            });
        }
    }

    public void unregisterMbean() {
        if (mbeanRegistered) {
            AccessController.doPrivileged(new PrivilegedAction<Object>() {

                @Override
                public Object run() {
                    DruidDataSourceStatManager.removeDataSource(DruidDataSource.this);
                    DruidDataSource.this.mbeanRegistered = false;
                    return null;
                }
            });
        }
    }

    public boolean isMbeanRegistered() {
        return mbeanRegistered;
    }
    //DruidDataSource类里的putLast方法，由上方的recycle方法触发
    boolean putLast(DruidConnectionHolder e, long lastActiveTimeMillis) {
        if (poolingCount >= maxActive || e.discard) {//池子已满，不加
            return false;
        }
        //刷新上次活跃时间，该时间很重要，直接影响连接检查的触发
        e.lastActiveTimeMillis = lastActiveTimeMillis;
        connections[poolingCount] = e;//放进连接池数组尾部
        incrementPoolingCount();//poolingCount++

        if (poolingCount > poolingPeak) {
            poolingPeak = poolingCount;
            poolingPeakTime = lastActiveTimeMillis;
        }
        //因为成功回收了一个连接，那就唤起一次所有因为获取不到连接而被阻塞的业务线程吧~（参考流程1.2）
        notEmpty.signal();
        notEmptySignalCount++;

        return true;
    }

    DruidConnectionHolder takeLast() throws InterruptedException, SQLException {
        try {
            while (poolingCount == 0) {
                emptySignal(); // send signal to CreateThread create connection

                if (failFast && isFailContinuous()) {
                    throw new DataSourceNotAvailableException(createError);
                }

                notEmptyWaitThreadCount++;
                if (notEmptyWaitThreadCount > notEmptyWaitThreadPeak) {
                    notEmptyWaitThreadPeak = notEmptyWaitThreadCount;
                }
                try {
                    notEmpty.await(); // signal by recycle or creator
                } finally {
                    notEmptyWaitThreadCount--;
                }
                notEmptyWaitCount++;

                if (!enable) {
                    connectErrorCountUpdater.incrementAndGet(this);
                    if (disableException != null) {
                        throw disableException;
                    }

                    throw new DataSourceDisableException();
                }
            }
        } catch (InterruptedException ie) {
            notEmpty.signal(); // propagate to non-interrupted thread
            notEmptySignalCount++;
            throw ie;
        }

        decrementPoolingCount();
        DruidConnectionHolder last = connections[poolingCount];
        connections[poolingCount] = null;

        return last;
    }

    //尝试从池子里获取连接
    private DruidConnectionHolder pollLast(long nanos) throws InterruptedException, SQLException {
        long estimate = nanos;

        for (;;) {
            if (poolingCount == 0) {//池子里的空闲连接为0，说明需要通知主流程3新增连接了
                // empty.signal，唤起主流程3新增连接
                emptySignal(); // send signal to CreateThread create connection


                if (failFast && isFailContinuous()) { //如果置为快速结束，则不阻塞业务线程，直接抛出异常
                    throw new DataSourceNotAvailableException(createError);
                }

                if (estimate <= 0) {
                    waitNanosLocal.set(nanos - estimate);
                    return null;
                }

                notEmptyWaitThreadCount++;//因为获取不到连接而陷入阻塞状态的业务线程数+1
                if (notEmptyWaitThreadCount > notEmptyWaitThreadPeak) {
                    notEmptyWaitThreadPeak = notEmptyWaitThreadCount;
                }

                try {
                    long startEstimate = estimate;
                    // 阻塞（挂起）estimate这么长的世界，期间如果被唤醒，则estimate就会被刷新成剩余等待时间
                    estimate = notEmpty.awaitNanos(estimate); // signal by
                                                              // recycle or
                                                              // creator
                    notEmptyWaitCount++;
                    notEmptyWaitNanos += (startEstimate - estimate);

                    if (!enable) {
                        connectErrorCountUpdater.incrementAndGet(this);

                        if (disableException != null) {
                            throw disableException;
                        }

                        throw new DataSourceDisableException();
                    }
                } catch (InterruptedException ie) {
                    // 期间线程被中断，则唤起一次其他处于阻塞状态的业务线程
                    notEmpty.signal(); // propagate to non-interrupted thread
                    notEmptySignalCount++;
                    throw ie;
                } finally {
                    notEmptyWaitThreadCount--;
                }

                if (poolingCount == 0) {//依然没有竞争到
                    if (estimate > 0) { //如果目标阻塞时间（maxWait）还没有用完，则继续尝试获取
                        continue;
                    }

                    waitNanosLocal.set(nanos - estimate);
                    return null;
                }
            }

            decrementPoolingCount(); //poolingCount--
            DruidConnectionHolder last = connections[poolingCount];//直接获取
            connections[poolingCount] = null;//获取后意味着连接已被借出，原有位置置空

            long waitNanos = nanos - estimate;//标记这次获取连接花了多长时间，连接够用时便为0
            last.setLastNotEmptyWaitNanos(waitNanos);

            return last;//返回
        }
    }

    private final void decrementPoolingCount() {
        poolingCount--;
    }

    private final void incrementPoolingCount() {
        poolingCount++;
    }

    @Override
    public Connection getConnection(String username, String password) throws SQLException {
        if (this.username == null
                && this.password == null
                && username != null
                && password != null) {
            this.username = username;
            this.password = password;

            return getConnection();
        }

        if (!StringUtils.equals(username, this.username)) {
            throw new UnsupportedOperationException("Not supported by DruidDataSource");
        }

        if (!StringUtils.equals(password, this.password)) {
            throw new UnsupportedOperationException("Not supported by DruidDataSource");
        }

        return getConnection();
    }

    public long getCreateCount() {
        return createCount;
    }

    public long getDestroyCount() {
        return destroyCount;
    }

    public long getConnectCount() {
        lock.lock();
        try {
            return connectCount;
        } finally {
            lock.unlock();
        }
    }

    public long getCloseCount() {
        return closeCount;
    }

    public long getConnectErrorCount() {
        return connectErrorCountUpdater.get(this);
    }

    @Override
    public int getPoolingCount() {
        lock.lock();
        try {
            return poolingCount;
        } finally {
            lock.unlock();
        }
    }

    public int getPoolingPeak() {
        lock.lock();
        try {
            return poolingPeak;
        } finally {
            lock.unlock();
        }
    }

    public Date getPoolingPeakTime() {
        if (poolingPeakTime <= 0) {
            return null;
        }

        return new Date(poolingPeakTime);
    }

    public long getRecycleCount() {
        return recycleCount;
    }

    public int getActiveCount() {
        lock.lock();
        try {
            return activeCount;
        } finally {
            lock.unlock();
        }
    }

    public void logStats() {
        final DruidDataSourceStatLogger statLogger = this.statLogger;
        if (statLogger == null) {
            return;
        }

        DruidDataSourceStatValue statValue = getStatValueAndReset();

        statLogger.log(statValue);
    }

    public DruidDataSourceStatValue getStatValueAndReset() {
        DruidDataSourceStatValue value = new DruidDataSourceStatValue();

        lock.lock();
        try {
            value.setPoolingCount(this.poolingCount);
            value.setPoolingPeak(this.poolingPeak);
            value.setPoolingPeakTime(this.poolingPeakTime);

            value.setActiveCount(this.activeCount);
            value.setActivePeak(this.activePeak);
            value.setActivePeakTime(this.activePeakTime);

            value.setConnectCount(this.connectCount);
            value.setCloseCount(this.closeCount);
            value.setWaitThreadCount(lock.getWaitQueueLength(notEmpty));
            value.setNotEmptyWaitCount(this.notEmptyWaitCount);
            value.setNotEmptyWaitNanos(this.notEmptyWaitNanos);
            value.setKeepAliveCheckCount(this.keepAliveCheckCount);

            // reset
            this.poolingPeak = 0;
            this.poolingPeakTime = 0;
            this.activePeak = 0;
            this.activePeakTime = 0;
            this.connectCount = 0;
            this.closeCount = 0;
            this.keepAliveCheckCount = 0;

            this.notEmptyWaitCount = 0;
            this.notEmptyWaitNanos = 0;
        } finally {
            lock.unlock();
        }

        value.setName(this.getName());
        value.setDbType(this.dbType);
        value.setDriverClassName(this.getDriverClassName());

        value.setUrl(this.getUrl());
        value.setUserName(this.getUsername());
        value.setFilterClassNames(this.getFilterClassNames());

        value.setInitialSize(this.getInitialSize());
        value.setMinIdle(this.getMinIdle());
        value.setMaxActive(this.getMaxActive());

        value.setQueryTimeout(this.getQueryTimeout());
        value.setTransactionQueryTimeout(this.getTransactionQueryTimeout());
        value.setLoginTimeout(this.getLoginTimeout());
        value.setValidConnectionCheckerClassName(this.getValidConnectionCheckerClassName());
        value.setExceptionSorterClassName(this.getExceptionSorterClassName());

        value.setTestOnBorrow(this.testOnBorrow);
        value.setTestOnReturn(this.testOnReturn);
        value.setTestWhileIdle(this.testWhileIdle);

        value.setDefaultAutoCommit(this.isDefaultAutoCommit());

        if (defaultReadOnly != null) {
            value.setDefaultReadOnly(defaultReadOnly);
        }
        value.setDefaultTransactionIsolation(this.getDefaultTransactionIsolation());

        value.setLogicConnectErrorCount(connectErrorCountUpdater.getAndSet(this, 0));

        value.setPhysicalConnectCount(createCountUpdater.getAndSet(this, 0));
        value.setPhysicalCloseCount(destroyCountUpdater.getAndSet(this, 0));
        value.setPhysicalConnectErrorCount(createErrorCountUpdater.getAndSet(this, 0));

        value.setExecuteCount(this.getAndResetExecuteCount());
        value.setErrorCount(errorCountUpdater.getAndSet(this, 0));
        value.setCommitCount(commitCountUpdater.getAndSet(this, 0));
        value.setRollbackCount(rollbackCountUpdater.getAndSet(this, 0));

        value.setPstmtCacheHitCount(cachedPreparedStatementHitCountUpdater.getAndSet(this,0));
        value.setPstmtCacheMissCount(cachedPreparedStatementMissCountUpdater.getAndSet(this, 0));

        value.setStartTransactionCount(startTransactionCountUpdater.getAndSet(this, 0));
        value.setTransactionHistogram(this.getTransactionHistogram().toArrayAndReset());

        value.setConnectionHoldTimeHistogram(this.getDataSourceStat().getConnectionHoldHistogram().toArrayAndReset());
        value.setRemoveAbandoned(this.isRemoveAbandoned());
        value.setClobOpenCount(this.getDataSourceStat().getClobOpenCountAndReset());
        value.setBlobOpenCount(this.getDataSourceStat().getBlobOpenCountAndReset());

        value.setSqlSkipCount(this.getDataSourceStat().getSkipSqlCountAndReset());
        value.setSqlList(this.getDataSourceStat().getSqlStatMapAndReset());

        return value;
    }

    public long getRemoveAbandonedCount() {
        return removeAbandonedCount;
    }

    // 这一个put方法是上面触发接收PhysicalConnectionInfo类型连接用的，之前说过，
    // 最终保存在池子里的连接对象都是DruidConnectionHolder类型，所以这里时进行一次包装，然后真正put进去的是更下面的put方法
    protected boolean put(PhysicalConnectionInfo physicalConnectionInfo) {
        DruidConnectionHolder holder = null;
        try {
            //包装成holder类型
            holder = new DruidConnectionHolder(DruidDataSource.this, physicalConnectionInfo);
        } catch (SQLException ex) {
            lock.lock();
            try {
                if (createScheduler != null) {
                    clearCreateTask(physicalConnectionInfo.createTaskId);
                }
            } finally {
                lock.unlock();
            }
            LOG.error("create connection holder error", ex);
            return false;
        }
        //真正放入池子
        return put(holder, physicalConnectionInfo.createTaskId);
    }

    //真正将连接对象放入池子
    private boolean put(DruidConnectionHolder holder, long createTaskId) {
        lock.lock();
        try {
            if (poolingCount >= maxActive) {
                //如果此时发现当前池子里的闲置连接数已经超过了maxActive，那么就不再往里面加了
                return false;
            }
            connections[poolingCount] = holder;//加在数组尾部
            incrementPoolingCount(); //poolingCount++

            if (poolingCount > poolingPeak) {
                poolingPeak = poolingCount;
                poolingPeakTime = System.currentTimeMillis();
            }

            //唤起一个因为拿不到连接对象而发生阻塞的业务线程，让其再次进入运行状态，进行获取连接竞争
            notEmpty.signal();
            notEmptySignalCount++;

            if (createScheduler != null) { //模式未启用
                clearCreateTask(createTaskId);

                if (poolingCount + createTaskCount < notEmptyWaitThreadCount //
                    && activeCount + poolingCount + createTaskCount < maxActive) {
                    emptySignal();
                }
            }
        } finally {
            lock.unlock();
        }
        return true;
    }

    public class CreateConnectionTask implements Runnable {

        private int errorCount   = 0;
        private boolean initTask = false;
        private final long taskId;

        public CreateConnectionTask() {
            taskId = createTaskIdSeedUpdater.getAndIncrement(DruidDataSource.this);
        }

        public CreateConnectionTask(boolean initTask) {
            taskId = createTaskIdSeedUpdater.getAndIncrement(DruidDataSource.this);
            this.initTask = initTask;
        }

        @Override
        public void run() {
            runInternal();
        }

        private void runInternal() {
            for (;;) {

                // addLast
                lock.lock();
                try {
                    if (closed || closing) {
                        clearCreateTask(taskId);
                        return;
                    }

                    boolean emptyWait = true;

                    if (createError != null && poolingCount == 0) {
                        emptyWait = false;
                    }

                    if (emptyWait) {
                        // 必须存在线程等待，才创建连接
                        if (poolingCount >= notEmptyWaitThreadCount //
                                && (!(keepAlive && activeCount + poolingCount < minIdle)) // 在keepAlive场景不能放弃创建
                                && (!initTask) // 线程池初始化时的任务不能放弃创建
                                && !isFailContinuous() // failContinuous时不能放弃创建，否则会无法创建线程
                                && !isOnFatalError() // onFatalError时不能放弃创建，否则会无法创建线程
                        ) {
                            clearCreateTask(taskId);
                            return;
                        }

                        // 防止创建超过maxActive数量的连接
                        if (activeCount + poolingCount >= maxActive) {
                            clearCreateTask(taskId);
                            return;
                        }
                    }
                } finally {
                    lock.unlock();
                }

                PhysicalConnectionInfo physicalConnection = null;

                try {
                    physicalConnection = createPhysicalConnection();
                } catch (OutOfMemoryError e) {
                    LOG.error("create connection OutOfMemoryError, out memory. ", e);

                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        // fail over retry attempts
                        setFailContinuous(true);
                        if (failFast) {
                            lock.lock();
                            try {
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        this.errorCount = 0; // reset errorCount
                        if (closing || closed) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        createSchedulerFuture = createScheduler.schedule(this, timeBetweenConnectErrorMillis, TimeUnit.MILLISECONDS);
                        return;
                    }
                } catch (SQLException e) {
                    LOG.error("create connection SQLException, url: " + jdbcUrl, e);

                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        // fail over retry attempts
                        setFailContinuous(true);
                        if (failFast) {
                            lock.lock();
                            try {
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        this.errorCount = 0; // reset errorCount
                        if (closing || closed) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        createSchedulerFuture = createScheduler.schedule(this, timeBetweenConnectErrorMillis, TimeUnit.MILLISECONDS);
                        return;
                    }
                } catch (RuntimeException e) {
                    LOG.error("create connection RuntimeException", e);
                    // unknow fatal exception
                    setFailContinuous(true);
                    continue;
                } catch (Error e) {
                    lock.lock();
                    try {
                        clearCreateTask(taskId);
                    } finally {
                        lock.unlock();
                    }
                    LOG.error("create connection Error", e);
                    // unknow fatal exception
                    setFailContinuous(true);
                    break;
                } catch (Throwable e) {
                    lock.lock();
                    try {
                        clearCreateTask(taskId);
                    } finally {
                        lock.unlock();
                    }

                    LOG.error("create connection unexecpted error.", e);
                    break;
                }

                if (physicalConnection == null) {
                    continue;
                }

                physicalConnection.createTaskId = taskId;
                boolean result = put(physicalConnection);
                if (!result) {
                    JdbcUtils.close(physicalConnection.getPhysicalConnection());
                    LOG.info("put physical connection to pool failed.");
                }
                break;
            }
        }
    }
    //DruidDataSource的内部类，对应主流程3，用来补充连接
    public class CreateConnectionThread extends Thread {

        public CreateConnectionThread(String name){
            super(name);//重置线程名称
            this.setDaemon(true);//标记为守护线程
        }

        //run方法
        public void run() {
            initedLatch.countDown(); //通知init（主流程2）自己已经启动成功

            long lastDiscardCount = 0;
            int errorCount = 0;
            for (;;) {//死循环
                // addLast
                try {
                    lock.lockInterruptibly(); //锁获取
                } catch (InterruptedException e2) {
                    break;
                }

                long discardCount = DruidDataSource.this.discardCount;
                //当前丢弃连接数与最后一次丢弃连接数的差值大于0，说明又发生了丢弃连接的现象，该条件会促进连接的创建
                boolean discardChanged = discardCount - lastDiscardCount > 0;
                lastDiscardCount = discardCount;

                try {
                    boolean emptyWait = true;

                    if (createError != null
                            && poolingCount == 0
                            && !discardChanged) {
                        emptyWait = false;
                    }

                    if (emptyWait
                            && asyncInit && createCount < initialSize) {
                        emptyWait = false;
                    }

                    if (emptyWait) {
                        // 必须存在线程等待，才创建连接
                        if (poolingCount >= notEmptyWaitThreadCount //
                                && (!(keepAlive && activeCount + poolingCount < minIdle))
                                && !isFailContinuous()
                        ) {
                            empty.await(); //不需要创建连接时，阻塞（挂起）
                        }

                        // 防止创建超过maxActive数量的连接
                        if (activeCount + poolingCount >= maxActive) {
                            empty.await(); //超出限制依然挂起，不再新增连接
                            continue;
                        }
                    }

                } catch (InterruptedException e) {
                    lastCreateError = e;
                    lastErrorTimeMillis = System.currentTimeMillis();

                    if (!closing) {
                        LOG.error("create connection Thread Interrupted, url: " + jdbcUrl, e);
                    }
                    break;
                } finally {
                    lock.unlock(); //锁释放
                }
                //从上面的程序走到这里，说明该线程被成功唤起，则进行新建连接
                PhysicalConnectionInfo connection = null;

                try {
                    connection = createPhysicalConnection();//利用驱动程序新建物理连接
                } catch (SQLException e) {
                    LOG.error("create connection SQLException, url: " + jdbcUrl + ", errorCode " + e.getErrorCode()
                              + ", state " + e.getSQLState(), e);

                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        // fail over retry attempts
                        setFailContinuous(true);
                        if (failFast) {
                            lock.lock();
                            try {
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            break;
                        }

                        try {
                            Thread.sleep(timeBetweenConnectErrorMillis);
                        } catch (InterruptedException interruptEx) {
                            break;
                        }
                    }
                } catch (RuntimeException e) {
                    LOG.error("create connection RuntimeException", e);
                    setFailContinuous(true);
                    continue;
                } catch (Error e) {
                    LOG.error("create connection Error", e);
                    setFailContinuous(true);
                    break;
                }

                if (connection == null) {
                    continue;//新建失败后再次尝试
                }

                boolean result = put(connection);//尝试放入池子
                if (!result) {
                    JdbcUtils.close(connection.getPhysicalConnection());
                    LOG.info("put physical connection to pool failed.");
                }

                errorCount = 0; // reset errorCount
            }
        }
    }
    //连接池瘦身，参考主流程4
    public class DestroyConnectionThread extends Thread {

        public DestroyConnectionThread(String name){
            super(name); //给线程重命名
            this.setDaemon(true); //标记为守护线程
        }
        //run方法
        public void run() {
            initedLatch.countDown(); //通知init（主流程2）自己已经启动成功

            for (;;) {//死循环
                // 从前面开始删除
                try {
                    if (closed) {
                        break;
                    }
                    //检查时间间隔，不启用（小于等于0时）则默认1s，事实上，druid对于该参数的缺省值是60s
                    if (timeBetweenEvictionRunsMillis > 0) {
                        Thread.sleep(timeBetweenEvictionRunsMillis);
                    } else {
                        Thread.sleep(1000); //默认1s
                    }

                    if (Thread.interrupted()) {
                        break;
                    }

                    destroyTask.run();//启动destroy的run方法（在下方）
                } catch (InterruptedException e) {
                    break;
                }
            }
        }

    }
    //DruidDataSource内部类
    public class DestroyTask implements Runnable {
        public DestroyTask() {

        }

        @Override
        public void run() {
            shrink(true, keepAlive);//连接池的检查&瘦身

            if (isRemoveAbandoned()) {//如果开启该属性，则进行强制回收检查
                removeAbandoned();
            }
        }

    }

    public class LogStatsThread extends Thread {

        public LogStatsThread(String name){
            super(name);
            this.setDaemon(true);
        }

        public void run() {
            try {
                for (;;) {
                    try {
                        logStats();
                    } catch (Exception e) {
                        LOG.error("logStats error", e);
                    }

                    Thread.sleep(timeBetweenLogStatsMillis);
                }
            } catch (InterruptedException e) {
                // skip
            }
        }
    }
    //回收长期未归还的连接（再次说明：该方法仅在removeAbandoned设置为true的情况下触发）
    public int removeAbandoned() {
        int removeCount = 0;

        long currrentNanos = System.nanoTime();
        //这个列表用于存放满足条件的真正需要强制回收的连接
        List<DruidPooledConnection> abandonedList = new ArrayList<DruidPooledConnection>();

        activeConnectionLock.lock();
        try {
            // 在removeAbandoned设置为true的情况下，所有被借出去的连接，都会被保存进activeConnections（参考主流程1），
            // 所以要进行“长期未归还”的检查，就是从activeConnections开始的
            Iterator<DruidPooledConnection> iter = activeConnections.keySet().iterator();

            for (; iter.hasNext();) {
                DruidPooledConnection pooledConnection = iter.next();

                if (pooledConnection.isRunning()) {
                    continue;//如果当前连接正在使用中（指的是正在execute），则不处理
                }
                //利用当前时间和连接被借出去时的时间，计算出连接被借出去的时间有多久
                long timeMillis = (currrentNanos - pooledConnection.getConnectedTimeNano()) / (1000 * 1000);
                //如果连接被借出去的时间超过removeAbandonedTimeoutMillis这个阈值，将会命中“主动归还”的逻辑检查
                if (timeMillis >= removeAbandonedTimeoutMillis) {
                    iter.remove();//先从activeConnections移除
                    pooledConnection.setTraceEnable(false);//标记为false，防止回收时重复removeactiveConnections，可以参考主流程5
                    abandonedList.add(pooledConnection);//放入“强制回收”队列
                }
            }
        } finally {
            activeConnectionLock.unlock();
        }

        if (abandonedList.size() > 0) {//如果“强制回收”队列大于0，说明有需要回收的连接
            for (DruidPooledConnection pooledConnection : abandonedList) {//循环这些连接
                final ReentrantLock lock = pooledConnection.lock;
                lock.lock();//拿到连接的锁
                try {
                    if (pooledConnection.isDisable()) {
                        continue;//已经被回收的，则不管
                    }
                } finally {
                    lock.unlock();
                }
                //触发回收连接对象（pooledConnection）里的holcder（注意这里其实是把pooledConnection对象里的holder给回收至连接池了，
                //pooledConnection对象本身会被销毁）
                JdbcUtils.close(pooledConnection);//这里触发的close，是DruidPooledConnection的close，也就是会触发recycle方法的close
                pooledConnection.abandond();//标记为
                removeAbandonedCount++;
                removeCount++;

                if (isLogAbandoned()) {//日志打印，忽略
                    StringBuilder buf = new StringBuilder();
                    buf.append("abandon connection, owner thread: ");
                    buf.append(pooledConnection.getOwnerThread().getName());
                    buf.append(", connected at : ");
                    buf.append(pooledConnection.getConnectedTimeMillis());
                    buf.append(", open stackTrace\n");

                    StackTraceElement[] trace = pooledConnection.getConnectStackTrace();
                    for (int i = 0; i < trace.length; i++) {
                        buf.append("\tat ");
                        buf.append(trace[i].toString());
                        buf.append("\n");
                    }

                    buf.append("ownerThread current state is " + pooledConnection.getOwnerThread().getState()
                               + ", current stackTrace\n");
                    trace = pooledConnection.getOwnerThread().getStackTrace();
                    for (int i = 0; i < trace.length; i++) {
                        buf.append("\tat ");
                        buf.append(trace[i].toString());
                        buf.append("\n");
                    }

                    LOG.error(buf.toString());
                }
            }
        }

        return removeCount;//返回本次被强制回收的连接个数
    }

    /** Instance key */
    protected String instanceKey = null;

    public Reference getReference() throws NamingException {
        final String className = getClass().getName();
        final String factoryName = className + "Factory"; // XXX: not robust
        Reference ref = new Reference(className, factoryName, null);
        ref.add(new StringRefAddr("instanceKey", instanceKey));
        ref.add(new StringRefAddr("url", this.getUrl()));
        ref.add(new StringRefAddr("username", this.getUsername()));
        ref.add(new StringRefAddr("password", this.getPassword()));
        // TODO ADD OTHER PROPERTIES
        return ref;
    }

    @Override
    public List<String> getFilterClassNames() {
        List<String> names = new ArrayList<String>();
        for (Filter filter : filters) {
            names.add(filter.getClass().getName());
        }
        return names;
    }

    public int getRawDriverMajorVersion() {
        int version = -1;
        if (this.driver != null) {
            version = driver.getMajorVersion();
        }
        return version;
    }

    public int getRawDriverMinorVersion() {
        int version = -1;
        if (this.driver != null) {
            version = driver.getMinorVersion();
        }
        return version;
    }

    public String getProperties() {
        Properties properties = new Properties();
        properties.putAll(connectProperties);
        if (properties.containsKey("password")) {
            properties.put("password", "******");
        }
        return properties.toString();
    }

    @Override
    public void shrink() {
        shrink(false, false);
    }

    public void shrink(boolean checkTime) {
        shrink(checkTime, keepAlive);
    }

    //连接池瘦身
    public void shrink(boolean checkTime, boolean keepAlive) {
        try {
            lock.lockInterruptibly();
        } catch (InterruptedException e) {
            return;
        }

        boolean needFill = false;
        int evictCount = 0;
        int keepAliveCount = 0;
        int fatalErrorIncrement = fatalErrorCount - fatalErrorCountLastShrink;
        fatalErrorCountLastShrink = fatalErrorCount;
        
        try {
            if (!inited) {
                return;
            }
            //根据poolingCount和minIdle计算出evictCheck的范围
            final int checkCount = poolingCount - minIdle;
            final long currentTimeMillis = System.currentTimeMillis();
            for (int i = 0; i < poolingCount; ++i) {//开始遍历连接池里闲置的连接
                DruidConnectionHolder connection = connections[i];

                if ((onFatalError || fatalErrorIncrement > 0) && (lastFatalErrorTimeMillis > connection.connectTimeMillis))  {
                    keepAliveConnections[keepAliveCount++] = connection;
                    continue;
                }

                if (checkTime) { //除非手动调用，不然经过主流程4触发，一般为true
                    if (phyTimeoutMillis > 0) {
                        long phyConnectTimeMillis = currentTimeMillis - connection.connectTimeMillis;
                        if (phyConnectTimeMillis > phyTimeoutMillis) {
                            evictConnections[evictCount++] = connection;
                            continue;
                        }
                    }
                    //计算闲置时间
                    long idleMillis = currentTimeMillis - connection.lastActiveTimeMillis;

                    if (idleMillis < minEvictableIdleTimeMillis
                            && idleMillis < keepAliveBetweenTimeMillis
                    ) { //如果闲置时间达不到检测&瘦身的阈值，则不处理
                        break;
                    }

                    if (idleMillis >= minEvictableIdleTimeMillis) {
                        //达到需要丢弃的阈值时，则判断连接下标是否在evictCheck范围，若在，则视为“可以丢弃的对象”放入evictConnections数组
                        if (checkTime && i < checkCount) {
                            evictConnections[evictCount++] = connection;
                            continue;
                            //达到必须要丢弃的阈值时，则不管是不是在evictCheck范围内，都直接放入“可以丢弃的对象”的evictConnections数组
                        } else if (idleMillis > maxEvictableIdleTimeMillis) {
                            evictConnections[evictCount++] = connection;
                            continue;
                        }
                    }
                    //如果上面的条件均没有命中，如果keepAlive为true，
                    // 则判断是不是超过了闲置连接检查其活性的频次阈值（即由keepAliveBetweenTimeMillis控制）

                    if (keepAlive && idleMillis >= keepAliveBetweenTimeMillis) {
                        keepAliveConnections[keepAliveCount++] = connection;
                    }
                } else {
                    if (i < checkCount) {
                        evictConnections[evictCount++] = connection;
                    } else {
                        break;
                    }
                }
            }

            int removeCount = evictCount + keepAliveCount;//这一批需要移除特殊处理的连接总数
            if (removeCount > 0) {
                //根据当前移除的元素，把剩余的元素移动至数组首部（参考流程4.1）
                System.arraycopy(connections, removeCount, connections, 0, poolingCount - removeCount);
                Arrays.fill(connections, poolingCount - removeCount, poolingCount, null);//剩余位置清空
                poolingCount -= removeCount;
            }
            keepAliveCheckCount += keepAliveCount;

            if (keepAlive && poolingCount + activeCount < minIdle) {
                needFill = true;
            }
        } finally {
            lock.unlock();
        }

        if (evictCount > 0) {//如果需要丢弃的连接数量大于0
            for (int i = 0; i < evictCount; ++i) {
                DruidConnectionHolder item = evictConnections[i];
                Connection connection = item.getConnection();
                JdbcUtils.close(connection);//直接关闭连接（这里是直接关闭驱动连接，不再放回池子）
                destroyCountUpdater.incrementAndGet(this);
            }
            Arrays.fill(evictConnections, null); //将evictConnections数组重新置空（方便下次使用）
        }

        if (keepAliveCount > 0) {//检测那些需要判活的连接数
            // keep order
            for (int i = keepAliveCount - 1; i >= 0; --i) {
                DruidConnectionHolder holer = keepAliveConnections[i];
                Connection connection = holer.getConnection();
                holer.incrementKeepAliveCheckCount();

                boolean validate = false;
                try {
                    this.validateConnection(connection);//检测其活性
                    validate = true;
                } catch (Throwable error) {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("keepAliveErr", error);
                    }
                    // skip
                }

                boolean discard = !validate;
                if (validate) {//检测通过
                    holer.lastKeepTimeMillis = System.currentTimeMillis();
                    boolean putOk = put(holer, 0L);//检测通过后，再次放入池子
                    if (!putOk) {//放不进去池子（说明已经达到连接池最大连接数阈值maxActive），则视为可以“直接抛弃”的连接
                        discard = true;
                    }
                }

                if (discard) {
                    try {
                        connection.close(); //如果可以抛弃，则直接关闭连接（直接调用驱动的close）
                    } catch (Exception e) {
                        // skip
                    }

                    lock.lock();
                    try {
                        discardCount++; //抛弃连接数累加

                        if (activeCount + poolingCount <= minIdle) {
                            emptySignal();//唤起主流程3追加连接对象
                        }
                    } finally {
                        lock.unlock();
                    }
                }
            }
            this.getDataSourceStat().addKeepAliveCheckCount(keepAliveCount);
            Arrays.fill(keepAliveConnections, null);//将keepAliveConnections数组重新置空（方便下次使用）
        }

        if (needFill) {
            lock.lock();
            try {
                int fillCount = minIdle - (activeCount + poolingCount + createTaskCount);
                for (int i = 0; i < fillCount; ++i) {
                    emptySignal();
                }
            } finally {
                lock.unlock();
            }
        } else if (onFatalError || fatalErrorIncrement > 0) {
            lock.lock();
            try {
                emptySignal();
            } finally {
                lock.unlock();
            }
        }
    }

    public int getWaitThreadCount() {
        lock.lock();
        try {
            return lock.getWaitQueueLength(notEmpty);
        } finally {
            lock.unlock();
        }
    }

    public long getNotEmptyWaitCount() {
        return notEmptyWaitCount;
    }

    public int getNotEmptyWaitThreadCount() {
        lock.lock();
        try {
            return notEmptyWaitThreadCount;
        } finally {
            lock.unlock();
        }
    }

    public int getNotEmptyWaitThreadPeak() {
        lock.lock();
        try {
            return notEmptyWaitThreadPeak;
        } finally {
            lock.unlock();
        }
    }

    public long getNotEmptySignalCount() {
        return notEmptySignalCount;
    }

    public long getNotEmptyWaitMillis() {
        return notEmptyWaitNanos / (1000 * 1000);
    }

    public long getNotEmptyWaitNanos() {
        return notEmptyWaitNanos;
    }

    public int getLockQueueLength() {
        return lock.getQueueLength();
    }

    public int getActivePeak() {
        return activePeak;
    }

    public Date getActivePeakTime() {
        if (activePeakTime <= 0) {
            return null;
        }

        return new Date(activePeakTime);
    }

    public String dump() {
        lock.lock();
        try {
            return this.toString();
        } finally {
            lock.unlock();
        }
    }

    public long getErrorCount() {
        return this.errorCount;
    }

    public String toString() {
        StringBuilder buf = new StringBuilder();

        buf.append("{");

        buf.append("\n\tCreateTime:\"");
        buf.append(Utils.toString(getCreatedTime()));
        buf.append("\"");

        buf.append(",\n\tActiveCount:");
        buf.append(getActiveCount());

        buf.append(",\n\tPoolingCount:");
        buf.append(getPoolingCount());

        buf.append(",\n\tCreateCount:");
        buf.append(getCreateCount());

        buf.append(",\n\tDestroyCount:");
        buf.append(getDestroyCount());

        buf.append(",\n\tCloseCount:");
        buf.append(getCloseCount());

        buf.append(",\n\tConnectCount:");
        buf.append(getConnectCount());

        buf.append(",\n\tConnections:[");
        for (int i = 0; i < poolingCount; ++i) {
            DruidConnectionHolder conn = connections[i];
            if (conn != null) {
                if (i != 0) {
                    buf.append(",");
                }
                buf.append("\n\t\t");
                buf.append(conn.toString());
            }
        }
        buf.append("\n\t]");

        buf.append("\n}");

        if (this.isPoolPreparedStatements()) {
            buf.append("\n\n[");
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder conn = connections[i];
                if (conn != null) {
                    if (i != 0) {
                        buf.append(",");
                    }
                    buf.append("\n\t{\n\tID:");
                    buf.append(System.identityHashCode(conn.getConnection()));
                    PreparedStatementPool pool = conn.getStatementPool();

                    buf.append(", \n\tpoolStatements:[");

                    int entryIndex = 0;
                    try {
                        for (Map.Entry<PreparedStatementKey, PreparedStatementHolder> entry : pool.getMap().entrySet()) {
                            if (entryIndex != 0) {
                                buf.append(",");
                            }
                            buf.append("\n\t\t{hitCount:");
                            buf.append(entry.getValue().getHitCount());
                            buf.append(",sql:\"");
                            buf.append(entry.getKey().getSql());
                            buf.append("\"");
                            buf.append("\t}");

                            entryIndex++;
                        }
                    } catch (ConcurrentModificationException e) {
                        // skip ..
                    }

                    buf.append("\n\t\t]");

                    buf.append("\n\t}");
                }
            }
            buf.append("\n]");
        }

        return buf.toString();
    }

    public List<Map<String, Object>> getPoolingConnectionInfo() {
        List<Map<String, Object>> list = new ArrayList<Map<String, Object>>();
        lock.lock();
        try {
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder connHolder = connections[i];
                Connection conn = connHolder.getConnection();

                Map<String, Object> map = new LinkedHashMap<String, Object>();
                map.put("id", System.identityHashCode(conn));
                map.put("connectionId", connHolder.getConnectionId());
                map.put("useCount", connHolder.getUseCount());
                if (connHolder.lastActiveTimeMillis > 0) {
                    map.put("lastActiveTime", new Date(connHolder.lastActiveTimeMillis));
                }
                if (connHolder.lastKeepTimeMillis > 0) {
                    map.put("lastKeepTimeMillis", new Date(connHolder.lastKeepTimeMillis));
                }
                map.put("connectTime", new Date(connHolder.getTimeMillis()));
                map.put("holdability", connHolder.getUnderlyingHoldability());
                map.put("transactionIsolation", connHolder.getUnderlyingTransactionIsolation());
                map.put("autoCommit", connHolder.underlyingAutoCommit);
                map.put("readoOnly", connHolder.isUnderlyingReadOnly());

                if (connHolder.isPoolPreparedStatements()) {
                    List<Map<String, Object>> stmtCache = new ArrayList<Map<String, Object>>();
                    PreparedStatementPool stmtPool = connHolder.getStatementPool();
                    for (PreparedStatementHolder stmtHolder : stmtPool.getMap().values()) {
                        Map<String, Object> stmtInfo = new LinkedHashMap<String, Object>();

                        stmtInfo.put("sql", stmtHolder.key.getSql());
                        stmtInfo.put("defaultRowPrefetch", stmtHolder.getDefaultRowPrefetch());
                        stmtInfo.put("rowPrefetch", stmtHolder.getRowPrefetch());
                        stmtInfo.put("hitCount", stmtHolder.getHitCount());

                        stmtCache.add(stmtInfo);
                    }

                    map.put("pscache", stmtCache);
                }
                map.put("keepAliveCheckCount", connHolder.getKeepAliveCheckCount());

                list.add(map);
            }
        } finally {
            lock.unlock();
        }
        return list;
    }

    public void logTransaction(TransactionInfo info) {
        long transactionMillis = info.getEndTimeMillis() - info.getStartTimeMillis();
        if (transactionThresholdMillis > 0 && transactionMillis > transactionThresholdMillis) {
            StringBuilder buf = new StringBuilder();
            buf.append("long time transaction, take ");
            buf.append(transactionMillis);
            buf.append(" ms : ");
            for (String sql : info.getSqlList()) {
                buf.append(sql);
                buf.append(";");
            }
            LOG.error(buf.toString(), new TransactionTimeoutException());
        }
    }

    @Override
    public String getVersion() {
        return VERSION.getVersionNumber();
    }

    @Override
    public JdbcDataSourceStat getDataSourceStat() {
        return dataSourceStat;
    }

    public Object clone() throws CloneNotSupportedException {
        return cloneDruidDataSource();
    }

    public DruidDataSource cloneDruidDataSource() {
        DruidDataSource x = new DruidDataSource();

        cloneTo(x);

        return x;
    }

    public Map<String, Object> getStatDataForMBean() {
        try {
            Map<String, Object> map = new HashMap<String, Object>();

            // 0 - 4
            map.put("Name", this.getName());
            map.put("URL", this.getUrl());
            map.put("CreateCount", this.getCreateCount());
            map.put("DestroyCount", this.getDestroyCount());
            map.put("ConnectCount", this.getConnectCount());

            // 5 - 9
            map.put("CloseCount", this.getCloseCount());
            map.put("ActiveCount", this.getActiveCount());
            map.put("PoolingCount", this.getPoolingCount());
            map.put("LockQueueLength", this.getLockQueueLength());
            map.put("WaitThreadCount", this.getNotEmptyWaitThreadCount());

            // 10 - 14
            map.put("InitialSize", this.getInitialSize());
            map.put("MaxActive", this.getMaxActive());
            map.put("MinIdle", this.getMinIdle());
            map.put("PoolPreparedStatements", this.isPoolPreparedStatements());
            map.put("TestOnBorrow", this.isTestOnBorrow());

            // 15 - 19
            map.put("TestOnReturn", this.isTestOnReturn());
            map.put("MinEvictableIdleTimeMillis", this.minEvictableIdleTimeMillis);
            map.put("ConnectErrorCount", this.getConnectErrorCount());
            map.put("CreateTimespanMillis", this.getCreateTimespanMillis());
            map.put("DbType", this.dbType);

            // 20 - 24
            map.put("ValidationQuery", this.getValidationQuery());
            map.put("ValidationQueryTimeout", this.getValidationQueryTimeout());
            map.put("DriverClassName", this.getDriverClassName());
            map.put("Username", this.getUsername());
            map.put("RemoveAbandonedCount", this.getRemoveAbandonedCount());

            // 25 - 29
            map.put("NotEmptyWaitCount", this.getNotEmptyWaitCount());
            map.put("NotEmptyWaitNanos", this.getNotEmptyWaitNanos());
            map.put("ErrorCount", this.getErrorCount());
            map.put("ReusePreparedStatementCount", this.getCachedPreparedStatementHitCount());
            map.put("StartTransactionCount", this.getStartTransactionCount());

            // 30 - 34
            map.put("CommitCount", this.getCommitCount());
            map.put("RollbackCount", this.getRollbackCount());
            map.put("LastError", JMXUtils.getErrorCompositeData(this.getLastError()));
            map.put("LastCreateError", JMXUtils.getErrorCompositeData(this.getLastCreateError()));
            map.put("PreparedStatementCacheDeleteCount", this.getCachedPreparedStatementDeleteCount());

            // 35 - 39
            map.put("PreparedStatementCacheAccessCount", this.getCachedPreparedStatementAccessCount());
            map.put("PreparedStatementCacheMissCount", this.getCachedPreparedStatementMissCount());
            map.put("PreparedStatementCacheHitCount", this.getCachedPreparedStatementHitCount());
            map.put("PreparedStatementCacheCurrentCount", this.getCachedPreparedStatementCount());
            map.put("Version", this.getVersion());

            // 40 -
            map.put("LastErrorTime", this.getLastErrorTime());
            map.put("LastCreateErrorTime", this.getLastCreateErrorTime());
            map.put("CreateErrorCount", this.getCreateErrorCount());
            map.put("DiscardCount", this.getDiscardCount());
            map.put("ExecuteQueryCount", this.getExecuteQueryCount());

            map.put("ExecuteUpdateCount", this.getExecuteUpdateCount());

            return map;
        } catch (JMException ex) {
            throw new IllegalStateException("getStatData error", ex);
        }
    }

    public Map<String, Object> getStatData() {
        final int activeCount;
        final int activePeak;
        final Date activePeakTime;

        final int poolingCount;
        final int poolingPeak;
        final Date poolingPeakTime;

        final long connectCount;
        final long closeCount;

        lock.lock();
        try {
            poolingCount = this.poolingCount;
            poolingPeak = this.poolingPeak;
            poolingPeakTime = this.getPoolingPeakTime();

            activeCount = this.activeCount;
            activePeak = this.activePeak;
            activePeakTime = this.getActivePeakTime();

            connectCount = this.connectCount;
            closeCount = this.closeCount;
        } finally {
            lock.unlock();
        }
        Map<String, Object> dataMap = new LinkedHashMap<String, Object>();

        dataMap.put("Identity", System.identityHashCode(this));
        dataMap.put("Name", this.getName());
        dataMap.put("DbType", this.dbType);
        dataMap.put("DriverClassName", this.getDriverClassName());

        dataMap.put("URL", this.getUrl());
        dataMap.put("UserName", this.getUsername());
        dataMap.put("FilterClassNames", this.getFilterClassNames());

        dataMap.put("WaitThreadCount", this.getWaitThreadCount());
        dataMap.put("NotEmptyWaitCount", this.getNotEmptyWaitCount());
        dataMap.put("NotEmptyWaitMillis", this.getNotEmptyWaitMillis());

        dataMap.put("PoolingCount", poolingCount);
        dataMap.put("PoolingPeak", poolingPeak);
        dataMap.put("PoolingPeakTime", poolingPeakTime);

        dataMap.put("ActiveCount", activeCount);
        dataMap.put("ActivePeak", activePeak);
        dataMap.put("ActivePeakTime", activePeakTime);

        dataMap.put("InitialSize", this.getInitialSize());
        dataMap.put("MinIdle", this.getMinIdle());
        dataMap.put("MaxActive", this.getMaxActive());

        dataMap.put("QueryTimeout", this.getQueryTimeout());
        dataMap.put("TransactionQueryTimeout", this.getTransactionQueryTimeout());
        dataMap.put("LoginTimeout", this.getLoginTimeout());
        dataMap.put("ValidConnectionCheckerClassName", this.getValidConnectionCheckerClassName());
        dataMap.put("ExceptionSorterClassName", this.getExceptionSorterClassName());

        dataMap.put("TestOnBorrow", this.isTestOnBorrow());
        dataMap.put("TestOnReturn", this.isTestOnReturn());
        dataMap.put("TestWhileIdle", this.isTestWhileIdle());

        dataMap.put("DefaultAutoCommit", this.isDefaultAutoCommit());
        dataMap.put("DefaultReadOnly", this.getDefaultReadOnly());
        dataMap.put("DefaultTransactionIsolation", this.getDefaultTransactionIsolation());

        dataMap.put("LogicConnectCount", connectCount);
        dataMap.put("LogicCloseCount", closeCount);
        dataMap.put("LogicConnectErrorCount", this.getConnectErrorCount());

        dataMap.put("PhysicalConnectCount", this.getCreateCount());
        dataMap.put("PhysicalCloseCount", this.getDestroyCount());
        dataMap.put("PhysicalConnectErrorCount", this.getCreateErrorCount());

        dataMap.put("DiscardCount", this.getDiscardCount());

        dataMap.put("ExecuteCount", this.getExecuteCount());
        dataMap.put("ExecuteUpdateCount", this.getExecuteUpdateCount());
        dataMap.put("ExecuteQueryCount", this.getExecuteQueryCount());
        dataMap.put("ExecuteBatchCount", this.getExecuteBatchCount());
        dataMap.put("ErrorCount", this.getErrorCount());
        dataMap.put("CommitCount", this.getCommitCount());
        dataMap.put("RollbackCount", this.getRollbackCount());

        dataMap.put("PSCacheAccessCount", this.getCachedPreparedStatementAccessCount());
        dataMap.put("PSCacheHitCount", this.getCachedPreparedStatementHitCount());
        dataMap.put("PSCacheMissCount", this.getCachedPreparedStatementMissCount());

        dataMap.put("StartTransactionCount", this.getStartTransactionCount());
        dataMap.put("TransactionHistogram", this.getTransactionHistogramValues());

        dataMap.put("ConnectionHoldTimeHistogram", this.getDataSourceStat().getConnectionHoldHistogram().toArray());
        dataMap.put("RemoveAbandoned", this.isRemoveAbandoned());
        dataMap.put("ClobOpenCount", this.getDataSourceStat().getClobOpenCount());
        dataMap.put("BlobOpenCount", this.getDataSourceStat().getBlobOpenCount());
        dataMap.put("KeepAliveCheckCount", this.getDataSourceStat().getKeepAliveCheckCount());

        dataMap.put("KeepAlive", this.isKeepAlive());
        dataMap.put("FailFast", this.isFailFast());
        dataMap.put("MaxWait", this.getMaxWait());
        dataMap.put("MaxWaitThreadCount", this.getMaxWaitThreadCount());
        dataMap.put("PoolPreparedStatements", this.isPoolPreparedStatements());
        dataMap.put("MaxPoolPreparedStatementPerConnectionSize", this.getMaxPoolPreparedStatementPerConnectionSize());
        dataMap.put("MinEvictableIdleTimeMillis", this.minEvictableIdleTimeMillis);
        dataMap.put("MaxEvictableIdleTimeMillis", this.maxEvictableIdleTimeMillis);

        dataMap.put("LogDifferentThread", isLogDifferentThread());
        dataMap.put("RecycleErrorCount", getRecycleErrorCount());
        dataMap.put("PreparedStatementOpenCount", getPreparedStatementCount());
        dataMap.put("PreparedStatementClosedCount", getClosedPreparedStatementCount());

        dataMap.put("UseUnfairLock", isUseUnfairLock());
        dataMap.put("InitGlobalVariants", isInitGlobalVariants());
        dataMap.put("InitVariants", isInitVariants());
        return dataMap;
    }

    public JdbcSqlStat getSqlStat(int sqlId) {
        return this.getDataSourceStat().getSqlStat(sqlId);
    }

    public JdbcSqlStat getSqlStat(long sqlId) {
        return this.getDataSourceStat().getSqlStat(sqlId);
    }

    public Map<String, JdbcSqlStat> getSqlStatMap() {
        return this.getDataSourceStat().getSqlStatMap();
    }

    public Map<String, Object> getWallStatMap() {
        WallProviderStatValue wallStatValue = getWallStatValue(false);

        if (wallStatValue != null) {
            return wallStatValue.toMap();
        }

        return null;
    }

    public WallProviderStatValue getWallStatValue(boolean reset) {
        for (Filter filter : this.filters) {
            if (filter instanceof WallFilter) {
                WallFilter wallFilter = (WallFilter) filter;
                return wallFilter.getProvider().getStatValue(reset);
            }
        }

        return null;
    }

    public Lock getLock() {
        return lock;
    }

    @Override
    public boolean isWrapperFor(Class<?> iface) {
        for (Filter filter : this.filters) {
            if (filter.isWrapperFor(iface)) {
                return true;
            }
        }

        if (this.statLogger != null
            && (this.statLogger.getClass() == iface || DruidDataSourceStatLogger.class == iface)) {
            return true;
        }

        return super.isWrapperFor(iface);
    }

    @SuppressWarnings("unchecked")
    public <T> T unwrap(Class<T> iface) {
        for (Filter filter : this.filters) {
            if (filter.isWrapperFor(iface)) {
                return (T) filter;
            }
        }

        if (this.statLogger != null
            && (this.statLogger.getClass() == iface || DruidDataSourceStatLogger.class == iface)) {
            return (T) statLogger;
        }

        return super.unwrap(iface);
    }

    public boolean isLogDifferentThread() {
        return logDifferentThread;
    }

    public void setLogDifferentThread(boolean logDifferentThread) {
        this.logDifferentThread = logDifferentThread;
    }

    public DruidPooledConnection tryGetConnection() throws SQLException {
        if (poolingCount == 0) {
            return null;
        }
        return getConnection();
    }

    @Override
    public int fill() throws SQLException {
        return this.fill(this.maxActive);
    }

    @Override
    public int fill(int toCount) throws SQLException {
        if (closed) {
            throw new DataSourceClosedException("dataSource already closed at " + new Date(closeTimeMillis));
        }

        if (toCount < 0) {
            throw new IllegalArgumentException("toCount can't not be less than zero");
        }

        init();

        if (toCount > this.maxActive) {
            toCount = this.maxActive;
        }

        int fillCount = 0;
        for (;;) {
            try {
                lock.lockInterruptibly();
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            boolean fillable = this.isFillable(toCount);

            lock.unlock();

            if (!fillable) {
                break;
            }

            DruidConnectionHolder holder;
            try {
                PhysicalConnectionInfo pyConnInfo = createPhysicalConnection();
                holder = new DruidConnectionHolder(this, pyConnInfo);
            } catch (SQLException e) {
                LOG.error("fill connection error, url: " + this.jdbcUrl, e);
                connectErrorCountUpdater.incrementAndGet(this);
                throw e;
            }

            try {
                lock.lockInterruptibly();
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            try {
                if (!this.isFillable(toCount)) {
                    JdbcUtils.close(holder.getConnection());
                    LOG.info("fill connections skip.");
                    break;
                }
                this.putLast(holder, System.currentTimeMillis());
                fillCount++;
            } finally {
                lock.unlock();
            }
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("fill " + fillCount + " connections");
        }

        return fillCount;
    }

    private boolean isFillable(int toCount) {
        int currentCount = this.poolingCount + this.activeCount;
        if (currentCount >= toCount || currentCount >= this.maxActive) {
            return false;
        } else {
            return true;
        }
    }

    public boolean isFull() {
        lock.lock();
        try {
            return this.poolingCount + this.activeCount >= this.maxActive;
        } finally {
            lock.unlock();
        }
    }

    private void emptySignal() {
        if (createScheduler == null) {
            empty.signal();
            return;
        }

        if (createTaskCount >= maxCreateTaskCount) {
            return;
        }

        if (activeCount + poolingCount + createTaskCount >= maxActive) {
            return;
        }
        submitCreateTask(false);
    }

    @Override
    public ObjectName preRegister(MBeanServer server, ObjectName name) throws Exception {
        if (server != null) {
            try {
                if (server.isRegistered(name)) {
                    server.unregisterMBean(name);
                }
            } catch (Exception ex) {
                LOG.warn("DruidDataSource preRegister error", ex);
            }
        }
        return name;
    }

    @Override
    public void postRegister(Boolean registrationDone) {

    }

    @Override
    public void preDeregister() throws Exception {

    }

    @Override
    public void postDeregister() {

    }

    public boolean isClosed() {
        return this.closed;
    }

    public boolean isCheckExecuteTime() {
        return checkExecuteTime;
    }

    public void setCheckExecuteTime(boolean checkExecuteTime) {
        this.checkExecuteTime = checkExecuteTime;
    }
}
