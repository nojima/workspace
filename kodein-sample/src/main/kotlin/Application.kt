package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.database.DatabaseOperator
import io.javalin.Javalin
import org.kodein.di.Kodein
import org.kodein.di.generic.instance
import org.kodein.di.newInstance

class Application(private val diContainer: Kodein) : AutoCloseable {

    private val javalin: Javalin by diContainer.instance()

    fun run() {
        val operator by diContainer.newInstance { DatabaseOperator(instance()) }
        operator.migrate()

        javalin.start()
    }

    override fun close() {
        javalin.stop()
    }

    fun port() = javalin.port()
}
