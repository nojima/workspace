import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.InvalidUserNameException
import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

internal class UserNameTest {

    enum class NormalCase(val input: String) {
        TYPICAL("alice"),
        VALID_CHARS("azAZ09_"),
        SHORT("x"),
        LONG("x".repeat(UserName.MAX_LENGTH)),
    }

    @ParameterizedTest
    @EnumSource(NormalCase::class)
    @DisplayName("正常系")
    fun normalCases(case: NormalCase) {
        // Exercise
        val userName = UserName(case.input)

        // Verify
        assertThat(userName.toString()).isEqualTo(case.input)
    }

    enum class AbnormalCase(val input: String) {
        EMPTY(""),
        TOO_LONG("x".repeat(UserName.MAX_LENGTH + 1)),
        INVALID_CHAR("abc-def"),
    }

    @ParameterizedTest
    @EnumSource(AbnormalCase::class)
    @DisplayName("異常系")
    fun abnormalCases(case: AbnormalCase) {
        // Exercise & Verify
        assertThatThrownBy {
            UserName(case.input)
        }.isInstanceOf(InvalidUserNameException::class.java)
    }
}
