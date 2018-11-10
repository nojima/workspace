package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.GeneralErrorController
import com.ynojima.kodeinsample.controller.SignUpController
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import io.javalin.Javalin

fun main() {
    val userRepository = InMemoryUserRepository()

    val signUpUseCase = SignUpUseCase(userRepository)
    val getUserUseCase = GetUserUseCase(userRepository)

    val app = Javalin.create().apply {
        port(7000)
    }

    GeneralErrorController().mount(app)
    SignUpController(signUpUseCase).mount(app)
    GetUserController(getUserUseCase).mount(app)

    app.start()
}
