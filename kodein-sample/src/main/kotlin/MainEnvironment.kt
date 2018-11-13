package com.ynojima.kodeinsample

import com.ynojima.kodeinsample.controller.GeneralErrorController
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.SignUpController
import com.ynojima.kodeinsample.database.MySqlDataSourceFactory
import com.ynojima.kodeinsample.repository.Transactional
import com.ynojima.kodeinsample.repository.impl.MySqlTransactional
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import io.javalin.Javalin
import org.kodein.di.Kodein
import org.kodein.di.generic.bind
import org.kodein.di.generic.instance
import org.kodein.di.generic.singleton
import org.kodein.di.generic.with
import javax.sql.DataSource

object MainEnvironment {
    val diContainer = Kodein {
        bind<DataSource>() with singleton {
            MySqlDataSourceFactory.create("localhost", 3306, "kodein_sample", "root", "")
        }

        bind<Transactional>() with singleton { MySqlTransactional(instance()) }

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
}
