package micronaut.hello.world

import io.micronaut.http.MediaType
import io.micronaut.http.annotation.Controller
import io.micronaut.http.annotation.Get
import javax.inject.Inject

@Controller
class HelloController @Inject constructor(val greeter: Greeter){
    @Get("/hello", produces = [MediaType.TEXT_PLAIN])
    fun index(): String {
        return greeter.hello()
    }
}
