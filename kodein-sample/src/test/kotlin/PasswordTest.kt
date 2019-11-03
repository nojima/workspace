import com.google.common.truth.Truth.assertThat
import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.exception.InvalidPasswordException
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

internal class PasswordTest {

    enum class NormalCase(val input: String) {
        TYPICAL("Open Sesame 123"),
        SHORT("x".repeat(Password.MIN_LENGTH)),
        LONG("x".repeat(Password.MAX_LENGTH)),
        SYMBOLS(" !\"#$%&'()-=^~\\|`@[{;+:*]},<.>/?_"),
    }

    @ParameterizedTest
    @EnumSource(NormalCase::class)
    @DisplayName("正常系")
    fun normalCases(case: NormalCase) {
        // Exercise
        val password = Password(case.input)

        // Verify
        assertThat(password.toString()).isEqualTo(case.input)
    }

    enum class AbnormalCase(val input: String) {
        EMPTY(""),
        TOO_SHORT("x".repeat(Password.MIN_LENGTH - 1)),
        TOO_LONG("x".repeat(Password.MAX_LENGTH + 1)),
    }

    @ParameterizedTest
    @EnumSource(AbnormalCase::class)
    @DisplayName("異常系")
    fun abnormalCases(case: AbnormalCase) {
        // Exercise & Verify
        assertThrows<InvalidPasswordException> {
            Password(case.input)
        }
    }
}
