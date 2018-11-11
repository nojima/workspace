package com.ynojima.kodeinsample.controller

import com.ynojima.kodeinsample.exception.NotFoundException
import com.ynojima.kodeinsample.exception.ValidationException
import io.javalin.Context
import io.javalin.Javalin
import org.slf4j.LoggerFactory

class GeneralErrorController {

    companion object {
        val log = LoggerFactory.getLogger(GeneralErrorController::class.java)!!
    }

    fun mount(router: Javalin) {
        router.exception(NotFoundException::class.java, this::notFound)
        router.exception(ValidationException::class.java, this::invalidRequest)
        router.exception(Exception::class.java, this::internalServerError)
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
        log.error("Internal server error", e)
        ctx.status(500)
        ctx.result("Internal server error")
    }
}
