package controller

import com.nhaarman.mockitokotlin2.*
import com.ynojima.kodeinsample.*
import com.ynojima.kodeinsample.controller.SignUpController
import com.ynojima.kodeinsample.controller.SignUpController.SignUpRequestBody
import com.ynojima.kodeinsample.controller.SignUpController.SignUpResponseBody
import com.ynojima.kodeinsample.exception.DuplicatedUserNameException
import com.ynojima.kodeinsample.exception.InvalidPasswordException
import com.ynojima.kodeinsample.exception.InvalidUserNameException
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

internal class SignUpControllerTest {
    private val signUpUseCase = mock<SignUpUseCase>()
    private val app = TestJavalin.create().also {
        SignUpController(signUpUseCase).mount(it)
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
    @DisplayName("サインアップ 正常系")
    fun signUp() {
        // Setup
        val alice = User(UserId(42), UserName("alice"), Password("open sesame"))
        whenever(signUpUseCase.signUp(alice.name, alice.password)).doReturn(alice)

        // Exercise
        val req = SignUpRequestBody(userName = "alice", password = "open sesame")
        val res = TestHttpClient(app.port()).request("POST", "/users", req)

        // Verify
        val body = res.body!!.parse<SignUpResponseBody>()
        assertThat(body.userId).isEqualTo(42)
        assertThat(body.userName).isEqualTo("alice")
        assertThat(res.code).isEqualTo(200)
    }

    enum class ErrorCase(val expectedStatus: Int, val exception: Exception) {
        DUPLICATED_USER(400, DuplicatedUserNameException("Boom!", UserName("alice"))),
        INVALID_USER_NAME(400, InvalidUserNameException("Boom!", "invalid")),
        INVALID_PASSWORD(400, InvalidPasswordException("Boom!"))
    }

    @ParameterizedTest
    @EnumSource(ErrorCase::class)
    @DisplayName("サインアップ 異常系")
    fun signUpReturnsError(errorCase: ErrorCase) {
        // Setup
        whenever(signUpUseCase.signUp(any(), any())).doThrow(errorCase.exception)

        // Exercise
        val req = SignUpRequestBody(userName = "alice", password = "open sesame")
        val res = TestHttpClient(app.port()).request("POST", "/users", req)

        // Verify
        assertThat(res.code).isEqualTo(errorCase.expectedStatus)
    }
}
