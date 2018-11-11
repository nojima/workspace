package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.controller.GeneralErrorController
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.SignUpController
import com.ynojima.kodeinsample.repository.Transactional
import com.ynojima.kodeinsample.repository.impl.InMemoryTransactional
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import com.zaxxer.hikari.HikariDataSource
import io.javalin.Javalin
import org.kodein.di.Kodein
import org.kodein.di.generic.bind
import org.kodein.di.generic.instance
import org.kodein.di.generic.singleton
import org.kodein.di.generic.with
import javax.sql.DataSource

fun dependencies() = Kodein {
    bind<DataSource>() with singleton {
        dataSource("localhost", 3306, "kodein_sample", "root", "")
    }

    bind<Transactional>() with singleton { InMemoryTransactional() }

    bind<SignUpUseCase>() with singleton { SignUpUseCase(instance()) }
    bind<SignUpController>() with singleton { SignUpController(instance()) }

    bind<GetUserUseCase>() with singleton { GetUserUseCase(instance()) }
    bind<GetUserController>() with singleton { GetUserController(instance()) }

    bind<GeneralErrorController>() with singleton { GeneralErrorController() }

    constant(tag = "listeningPort") with 7000

    bind<Javalin>() with singleton {
        val app = Javalin.create().apply {
            port(instance(tag = "listeningPort"))
        }
        instance<GeneralErrorController>().mount(app)
        instance<SignUpController>().mount(app)
        instance<GetUserController>().mount(app)
        app
    }
}

fun dataSource(host: String, port: Int, dbName: String, user: String, password: String): HikariDataSource {
    val ds = HikariDataSource()
    ds.driverClassName = "org.mariadb.jdbc.Driver"
    ds.jdbcUrl = "jdbc:mysql://$host:$port/$dbName"
    ds.addDataSourceProperty("user", user)
    ds.addDataSourceProperty("password", password)
    ds.isAutoCommit = false
    return ds
}

fun main() {
    val container = dependencies()
    val app by container.instance<Javalin>()
    app.start()
}
