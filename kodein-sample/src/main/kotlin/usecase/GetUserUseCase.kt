package com.ynojima.kodeinsample.usecase

import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.exception.UserNotFoundException
import com.ynojima.kodeinsample.repository.Transactional
import com.ynojima.kodeinsample.repository.UserRepository

open class GetUserUseCase(private val transactional: Transactional) {
    open fun getUser(id: UserId): User {
        return transactional.execute { repos ->
            repos.userRepository.getUser(id)
                ?: throw UserNotFoundException("User not found: id=$id")
        }
    }
}
