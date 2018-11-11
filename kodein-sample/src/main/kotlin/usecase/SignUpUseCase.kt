package com.ynojima.kodeinsample.usecase

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.DuplicatedUserNameException
import com.ynojima.kodeinsample.repository.Transactional

open class SignUpUseCase(private val transactional: Transactional) {
    open fun signUp(userName: UserName, password: Password): User {
        return transactional.execute { repos ->
            val userRepository = repos.userRepository
            if (userRepository.getUserByName(userName) != null) {
                throw DuplicatedUserNameException("Specified user already exists", userName)
            }
            userRepository.createUser(userName, password)
        }
    }
}
