package com.ynojima.kodeinsample.database

import org.flywaydb.core.Flyway
import javax.sql.DataSource

class DatabaseOperator(dataSource: DataSource) {
    private val flyway = Flyway.configure()
        .dataSource(dataSource)
        .load()

    fun migrate() {
        flyway.migrate()
    }

    fun drop() {
        flyway.clean()
    }
}
