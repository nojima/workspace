package com.ynojima.kodeinsample.controller

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import io.javalin.Context
import io.javalin.Javalin

class SignUpController(
    private val signUpUseCase: SignUpUseCase
) {
    fun mount(router: Javalin) {
        router.post("/users", this::signUp)
    }

    data class SignUpRequestBody(
        val userName: String,
        val password: String)
    data class SignUpResponseBody(
        val userId: Long,
        val userName: String)

    private fun signUp(ctx: Context) {
        val req = ctx.bodyAsClass(SignUpRequestBody::class.java)
        val user = signUpUseCase.signUp(UserName(req.userName), Password(req.password))
        val res = SignUpResponseBody(userId = user.id.toLong(), userName = user.name.toString())
        ctx.json(res)
    }
}