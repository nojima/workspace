package usecase

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.UserNotFoundException
import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

internal class GetUserUseCaseTest {
    private val userRepository = InMemoryUserRepository()
    private val sut = GetUserUseCase(userRepository)

    @Test
    @DisplayName("ユーザーを取得できる")
    fun getUser() {
        // Setup
        val alice = userRepository.createUser(UserName("alice"), Password("open sesame"))

        // Exercise
        val user = sut.getUser(alice.id)

        // Verify
        assertThat(user.id).isEqualTo(alice.id)
        assertThat(user.name).isEqualTo(UserName("alice"))
        assertThat(user.password).isEqualTo(Password("open sesame"))
    }

    @Test
    @DisplayName("存在しないユーザーを取得しようとすると例外が発生する")
    fun getNonexistentUser() {
        // Exercise & Verify
        assertThatThrownBy {
            sut.getUser(UserId(100))
        }.isInstanceOf(UserNotFoundException::class.java)
    }
}
