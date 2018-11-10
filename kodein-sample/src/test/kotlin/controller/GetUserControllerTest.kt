package controller

import com.fasterxml.jackson.module.kotlin.jacksonObjectMapper
import com.fasterxml.jackson.module.kotlin.readValue
import com.nhaarman.mockitokotlin2.doReturn
import com.nhaarman.mockitokotlin2.mock
import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.controller.GeneralErrorController
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.GetUserController.GetUserResponseBody
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import io.javalin.Javalin
import okhttp3.OkHttpClient
import okhttp3.Request
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

internal class GetUserControllerTest {
    companion object {
        private val client = OkHttpClient()
        private val objectMapper = jacksonObjectMapper()
    }

    private fun setupTestApplication(): Javalin {
        val app = Javalin.create().apply {
            port(0)
        }
        GeneralErrorController().mount(app)

        val alice = User(UserId(42), UserName("alice"), Password("open sesame"))
        val getUserUseCase = mock<GetUserUseCase> {
            on { getUser(alice.id) } doReturn alice
        }

        GetUserController(getUserUseCase).mount(app)
        app.start()

        return app
    }

    @Test
    fun getUser() {
        val app = setupTestApplication()
        val endpoint = "http://localhost:${app.port()}"

        val req = Request.Builder()
            .get()
            .url("$endpoint/users/42")
            .build()
        client.newCall(req).execute().use { res ->
            if (!res.isSuccessful) {
                val body = res.body()?.string() ?: ""
                throw RuntimeException("Error response returned: status=${res.code()}, body=${body.trim()}")
            }
            val body: GetUserResponseBody = objectMapper.readValue(res.body()!!.byteStream())

            assertThat(body.userId).isEqualTo(42)
            assertThat(body.userName).isEqualTo("alice")
        }
    }
}
