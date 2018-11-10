package com.ynojima.kodeinsample.rest

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.NotFoundException
import com.ynojima.kodeinsample.exception.ValidationException
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import io.javalin.Context
import io.javalin.Javalin

class Server(
    private val signUpUseCase: SignUpUseCase,
    private val getUserUseCase: GetUserUseCase
) {

    fun start() {
        val app = Javalin.create().start(7000)
        app.exception(NotFoundException::class.java, this::notFound)
        app.exception(ValidationException::class.java, this::invalidRequest)
        app.exception(Exception::class.java, this::internalServerError)
        app.get("/users/:id", this::getUser)
        app.post("/users", this::signUp)
    }

    private fun notFound(e: NotFoundException, ctx: Context) {
        ctx.status(404)
        ctx.result(e.message ?: "Not found")
    }

    private fun invalidRequest(e: ValidationException, ctx: Context) {
        ctx.status(400)
        ctx.result(e.message ?: "Invalid request")
    }

    private fun internalServerError(@Suppress("UNUSED_PARAMETER") e: Exception, ctx: Context) {
        ctx.status(500)
        ctx.result("Internal server error")
    }

    data class GetUserResponseBody(
        val userId: Long,
        val userName: String
    )

    private fun getUser(ctx: Context) {
        val id = ctx.validatedPathParam("id").asLong().getOrThrow()
        val user = getUserUseCase.getUser(UserId(id))
        val res = GetUserResponseBody(userId = user.id.toLong(), userName = user.name.toString())
        ctx.json(res)
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
