package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import com.ynojima.kodeinsample.rest.GetUserController
import com.ynojima.kodeinsample.rest.Server
import com.ynojima.kodeinsample.rest.SignUpController
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase

fun main() {
    val userRepository = InMemoryUserRepository()

    val signUpUseCase = SignUpUseCase(userRepository)
    val getUserUseCase = GetUserUseCase(userRepository)

    val signUpController = SignUpController(signUpUseCase)
    val getUserController = GetUserController(getUserUseCase)

    val server = Server(getUserController, signUpController, 7000)
    server.start()
}
