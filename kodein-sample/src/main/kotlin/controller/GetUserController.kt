package com.ynojima.kodeinsample.controller

import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import io.javalin.Context
import io.javalin.Javalin

class GetUserController(
    router: Javalin,
    private val getUserUseCase: GetUserUseCase
) {
    init {
        router.get("/users/:id", this::getUser)
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
}
