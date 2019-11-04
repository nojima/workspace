import com.ynojima.kodeinsample.controller.GeneralErrorController
import io.javalin.Javalin

object TestJavalin {
    fun new(): Javalin {
        val app = Javalin.create { config ->
            config.showJavalinBanner = false
            config.enableDevLogging()
        }
        GeneralErrorController(app)
        return app
    }
}
