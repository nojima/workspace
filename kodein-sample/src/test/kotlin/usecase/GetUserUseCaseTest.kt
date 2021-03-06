package usecase

import com.google.common.truth.Truth.assertThat
import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.exception.UserNotFoundException
import com.ynojima.kodeinsample.repository.impl.InMemoryTransactional
import com.ynojima.kodeinsample.usecase.GetUserUseCase
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

internal class GetUserUseCaseTest {
    private val transactional = InMemoryTransactional()
    private val sut = GetUserUseCase(transactional)

    @Test
    @DisplayName("ユーザーを取得できる")
    fun getUser() {
        // Setup
        val alice = transactional.execute { repo ->
            repo.userRepository.createUser(UserName("alice"), Password("open sesame"))
        }

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
        assertThrows<UserNotFoundException> {
            sut.getUser(UserId(100))
        }
    }
}
