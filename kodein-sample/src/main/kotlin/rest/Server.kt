package com.ynojima.kodeinsample.rest

import io.javalin.Javalin

class Server {
    data class HelloWorldResponse(
        val hello: String,
        val world: List<Int>)

    fun start() {
        val app = Javalin.create().start(7000)
        app.get("/") { ctx ->
            val res = HelloWorldResponse(
                hello = "Hello, World!!",
                world = listOf(1, 2, 3, 4, 5))
            ctx.json(res)
        }
    }
}