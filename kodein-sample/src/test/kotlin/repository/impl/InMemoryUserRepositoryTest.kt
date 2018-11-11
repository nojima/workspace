package repository.impl

import com.ynojima.kodeinsample.repository.impl.InMemoryTransactional

internal class InMemoryUserRepositoryTest : UserRepositoryTest() {
    override val transactional = InMemoryTransactional()
}
