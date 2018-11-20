package controller

import com.nhaarman.mockitokotlin2.any
import com.nhaarman.mockitokotlin2.doReturn
import com.nhaarman.mockitokotlin2.doThrow
import com.nhaarman.mockitokotlin2.mock
import com.nhaarman.mockitokotlin2.whenever
import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.TestHttpClient
import com.ynojima.kodeinsample.TestJavalin
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.controller.GetUserController
import com.ynojima.kodeinsample.controller.GetUserController.GetUserResponseBody
import com.ynojima.kodeinsample.exception.UserNotFoundException
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

internal class GetUserControllerTest {
    private val getUserUseCase = mock<GetUserUseCase>()
    private val app = TestJavalin.create().also {
        GetUserController(it, getUserUseCase)
    }

    @BeforeEach
    fun start() {
        app.start()
    }

    @AfterEach
    fun stop() {
        app.stop()
    }

    @Test
    @DisplayName("ユーザーを取得する (正常系)")
    fun getUser() {
        // Setup
        val alice = User(UserId(42), UserName("alice"), Password("open sesame"))
        whenever(getUserUseCase.getUser(alice.id)).doReturn(alice)

        // Exercise
        val res = TestHttpClient(app.port()).request("GET", "/users/42")

        // Verify
        val body = res.body!!.parse<GetUserResponseBody>()
        assertThat(body.userId).isEqualTo(42)
        assertThat(body.userName).isEqualTo("alice")
        assertThat(res.code).isEqualTo(200)
    }

    @Test
    @DisplayName("UserNotFoundExceptionが発生すると404が返る")
    fun getNonexistentUser() {
        // Setup
        whenever(getUserUseCase.getUser(any())).doThrow(UserNotFoundException("Boom!"))

        // Exercise
        val res = TestHttpClient(app.port()).request("GET", "/users/42")

        // Verify
        assertThat(res.code).isEqualTo(404)
    }

    @Test
    @DisplayName("IDが不正な場合400が返る")
    fun invalidId() {
        // Exercise
        val res = TestHttpClient(app.port()).request("GET", "/users/hello")

        // Verify
        assertThat(res.code).isEqualTo(400)
    }
}
