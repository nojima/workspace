package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import com.ynojima.kodeinsample.rest.Server
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase

fun main() {
    val userRepository = InMemoryUserRepository()
    val signUpUseCase = SignUpUseCase(userRepository)
    val getUserUseCase = GetUserUseCase(userRepository)
    Server(signUpUseCase, getUserUseCase).start()
}
