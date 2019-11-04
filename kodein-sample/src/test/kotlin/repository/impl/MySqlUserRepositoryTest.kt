package repository.impl

import TestDataSourceFactory
import com.ynojima.kodeinsample.database.DatabaseOperator
import com.ynojima.kodeinsample.repository.Transactional
import com.ynojima.kodeinsample.repository.impl.MySqlTransactional

internal class MySqlUserRepositoryTest : UserRepositoryTest() {
    private val dataSource = TestDataSourceFactory.new()
    override val transactional: Transactional = MySqlTransactional(dataSource)

    init {
        DatabaseOperator(dataSource).drop()
        DatabaseOperator(dataSource).migrate()
    }
}
