package micronaut.hello.world

import io.micronaut.runtime.Micronaut

object Application {

    @JvmStatic
    fun main(args: Array<String>) {
        Micronaut.build()
                .packages("micronaut.hello.world")
                .mainClass(Application.javaClass)
                .start()
    }
}