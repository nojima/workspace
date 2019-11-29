package micronaut.hello.world

import javax.inject.Singleton

@Singleton
class EnglishGreeter : Greeter {
    override fun hello(): String {
        return "Hello, World!!"
    }
}
