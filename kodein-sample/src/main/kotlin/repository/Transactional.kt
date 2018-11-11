package com.ynojima.kodeinsample.repository

interface Transactional {
    fun <R> execute(block: (Repositories) -> R): R
}

data class Repositories(
    val userRepository: UserRepository
)
