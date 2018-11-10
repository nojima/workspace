package com.ynojima.kodeinsample.rest

import com.ynojima.kodeinsample.exception.NotFoundException
import com.ynojima.kodeinsample.exception.ValidationException
import io.javalin.Context
import io.javalin.Javalin

class Server(
    private val getUserController: GetUserController,
    private val signUpController: SignUpController,
    private val listeningPort: Int
) {

    fun start() {
        val app = Javalin.create()

        app.exception(NotFoundException::class.java, this::notFound)
        app.exception(ValidationException::class.java, this::invalidRequest)
        app.exception(Exception::class.java, this::internalServerError)

        getUserController.register(app)
        signUpController.register(app)

        app.start(listeningPort)
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
}
