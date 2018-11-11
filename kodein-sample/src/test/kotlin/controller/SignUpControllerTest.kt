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
import com.ynojima.kodeinsample.controller.SignUpController
import com.ynojima.kodeinsample.controller.SignUpController.SignUpRequestBody
import com.ynojima.kodeinsample.controller.SignUpController.SignUpResponseBody
import com.ynojima.kodeinsample.exception.DuplicatedUserNameException
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
    @DisplayName("正常系")
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

    enum class UseCaseErrorCase(val expectedStatus: Int, val exception: Exception) {
        DUPLICATED_USER(400, DuplicatedUserNameException("Boom!", UserName("alice"))),
        RUNTIME_ERROR(500, RuntimeException("Boom!")),
    }

    @ParameterizedTest
    @EnumSource(UseCaseErrorCase::class)
    @DisplayName("ユースケースが例外を投げるとき")
    fun useCaseThrowsException(case: UseCaseErrorCase) {
        // Setup
        whenever(signUpUseCase.signUp(any(), any())).doThrow(case.exception)

        // Exercise
        val req = SignUpRequestBody(userName = "alice", password = "open sesame")
        val res = TestHttpClient(app.port()).request("POST", "/users", req)

        // Verify
        assertThat(res.code).isEqualTo(case.expectedStatus)
    }

    enum class ValidationErrorCase(val expectedStatus: Int, val req: SignUpRequestBody) {
        INVALID_USER_NAME(400, SignUpRequestBody(userName = "alice@", password = "open sesame")),
        INVALID_PASSWORD(400, SignUpRequestBody(userName = "alice", password = "")),
    }

    @ParameterizedTest
    @EnumSource(ValidationErrorCase::class)
    @DisplayName("不正な入力が来たとき")
    fun validationErrors(case: ValidationErrorCase) {
        // Exercise
        val res = TestHttpClient(app.port()).request("POST", "/users", case.req)

        // Verify
        assertThat(res.code).isEqualTo(case.expectedStatus)
    }
}
