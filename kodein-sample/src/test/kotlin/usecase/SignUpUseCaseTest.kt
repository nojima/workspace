package usecase

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.DuplicatedUserNameException
import com.ynojima.kodeinsample.repository.impl.InMemoryTransactional
import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import com.ynojima.kodeinsample.usecase.SignUpUseCase
import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

internal class SignUpUseCaseTest {
    private val transactional = InMemoryTransactional()
    private val sut = SignUpUseCase(transactional)

    @Test
    @DisplayName("サインアップ (通常系)")
    fun signUp() {
        // Exercise
        val user = sut.signUp(UserName("alice"), Password("open sesame"))

        // Verify
        assertThat(user.id).isEqualTo(UserId(1))
        assertThat(user.name).isEqualTo(UserName("alice"))
        assertThat(user.password).isEqualTo(Password("open sesame"))
    }

    @Test
    @DisplayName("重複したユーザー名でサインアップすると例外が発生する")
    fun signUpWithDuplicatedUserName() {
        // Setup
        sut.signUp(UserName("alice"), Password("open sesame"))

        // Exercise & Verify
        assertThatThrownBy {
            sut.signUp(UserName("alice"), Password("open sesame"))
        }.isInstanceOf(DuplicatedUserNameException::class.java)
    }
}
