package com.ynojima.kodeinsample.database

import com.zaxxer.hikari.HikariDataSource
import javax.sql.DataSource

object MySqlDataSourceFactory {
    fun create(host: String, port: Int, dbName: String, user: String, password: String): DataSource {
        val ds = HikariDataSource()
        ds.driverClassName = "org.mariadb.jdbc.Driver"
        ds.jdbcUrl = "jdbc:mysql://$host:$port/$dbName"
        ds.addDataSourceProperty("user", user)
        ds.addDataSourceProperty("password", password)
        ds.isAutoCommit = false
        return ds
    }
}
