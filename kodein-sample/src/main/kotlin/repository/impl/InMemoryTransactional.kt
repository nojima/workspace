package com.ynojima.kodeinsample.repository.impl

import com.ynojima.kodeinsample.repository.Repositories
import com.ynojima.kodeinsample.repository.Transactional

class InMemoryTransactional : Transactional {
    private val userRepository = InMemoryUserRepository()

    override fun <R> execute(block: (Repositories) -> R): R {
        val repos = Repositories(userRepository = userRepository)
        return block(repos)
    }
}
