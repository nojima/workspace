package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.controller.GeneralErrorController
import io.javalin.Javalin

object TestJavalin {
    fun create(): Javalin {
        val app = Javalin.create().apply {
            // ランダムポートを使うようにする
            port(0)
        }
        GeneralErrorController(app)
        return app
    }
}
