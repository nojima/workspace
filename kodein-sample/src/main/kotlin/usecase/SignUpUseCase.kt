package com.ynojima.kodeinsample.usecase

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.DuplicatedUserNameException
import com.ynojima.kodeinsample.repository.UserRepository

open class SignUpUseCase(private val userRepository: UserRepository) {
    open fun signUp(userName: UserName, password: Password): User {
        if (userRepository.getUserByName(userName) != null) {
            throw DuplicatedUserNameException("Specified user already exists", userName)
        }
        return userRepository.createUser(userName, password)
    }
}
