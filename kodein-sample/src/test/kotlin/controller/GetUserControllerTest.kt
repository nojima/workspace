package controller

import com.nhaarman.mockitokotlin2.doReturn
import com.nhaarman.mockitokotlin2.mock
import com.ynojima.kodeinsample.*
import com.ynojima.kodeinsample.controller.GeneralErrorController
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.GetUserController.GetUserResponseBody
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import io.javalin.Javalin
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

internal class GetUserControllerTest {
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
    @DisplayName("ユーザーを取得する")
    fun getUser() {
        // Setup
        val app = setupTestApplication()
        val client = TestHttpClient(app.port())

        // Exercise
        val res = client.request("GET", "/users/42")

        // Verify
        val body = res.body!!.parse<GetUserResponseBody>()
        assertThat(body.userId).isEqualTo(42)
        assertThat(body.userName).isEqualTo("alice")
        assertThat(res.code).isEqualTo(200)
    }
}
