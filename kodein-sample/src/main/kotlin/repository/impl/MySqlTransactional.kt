package com.ynojima.kodeinsample.repository.impl

import com.ynojima.kodeinsample.repository.Repositories
import com.ynojima.kodeinsample.repository.Transactional
import kotliquery.sessionOf
import javax.sql.DataSource

class MySqlTransactional(private val dataSource: DataSource) : Transactional {
    override fun <R> execute(block: (Repositories) -> R): R {
        return sessionOf(dataSource).use { session ->
            session.transaction { tx ->
                val repos = Repositories(userRepository = MySqlUserRepository(tx))
                block(repos)
            }
        }
    }
}
