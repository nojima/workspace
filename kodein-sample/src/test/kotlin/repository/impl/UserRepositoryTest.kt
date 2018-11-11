package repository.impl

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.repository.Transactional
import com.ynojima.kodeinsample.repository.UserRepository
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

internal abstract class UserRepositoryTest {

    abstract val transactional: Transactional

    private fun transaction(block: (UserRepository) -> Unit) {
        transactional.execute { repos ->
            block(repos.userRepository)
        }
    }

    @BeforeEach
    fun addSampleUser() = transaction { userRepository ->
        userRepository.createUser(UserName("alice"), Password("open sesame"))
    }

    @Nested
    @DisplayName("IDを指定してユーザーを取得する")
    inner class GetUser {
        @Test
        @DisplayName("正常系")
        fun getUser() = transaction { sut ->
            // Exercise
            val user = sut.getUser(UserId(1))

            // Verify
            val expected = User(UserId(1), UserName("alice"), Password("open sesame"))
            assertThat(user).isEqualTo(expected)
        }

        @Test
        @DisplayName("存在しないユーザーを取得すると null が返る")
        fun getNonexistentUser() = transaction { sut ->
            // Exercise
            val user = sut.getUser(UserId(100))

            // Verify
            assertThat(user).isNull()
        }
    }

    @Nested
    @DisplayName("名前を指定してユーザーを取得する")
    inner class GetUserByName {
        @Test
        @DisplayName("正常系")
        fun getUserByName() = transaction { sut ->
            // Exercise
            val user = sut.getUserByName(UserName("alice"))

            // Verify
            val expected = User(UserId(1), UserName("alice"), Password("open sesame"))
            assertThat(user).isEqualTo(expected)
        }

        @Test
        @DisplayName("存在しないユーザーを取得すると null が返る")
        fun getNonexistentUserByName() = transaction { sut ->
            // Exercise
            val user = sut.getUserByName(UserName("notfound"))

            // Verify
            assertThat(user).isNull()
        }
    }

    @Nested
    @DisplayName("ユーザーを作成する")
    inner class CreateUser {
        @Test
        @DisplayName("正常系")
        fun createUser() = transaction { sut ->
            // Exercise
            val user = sut.createUser(UserName("bob"), Password("secret"))

            // Verify
            val actual = sut.getUser(user.id)
            val expected = User(user.id, UserName("bob"), Password("secret"))
            assertThat(actual).isEqualTo(expected)
        }

        @Test
        @DisplayName("長いユーザー名とパスワードを指定したとき")
        fun longUserNameAndPassword() = transaction { sut ->
            // Exercise
            val name = UserName("a".repeat(UserName.MAX_LENGTH))
            val password = Password("x".repeat(Password.MAX_LENGTH))
            val user = sut.createUser(name, password)

            // Verify
            val actual = sut.getUser(user.id)
            val expected = User(user.id, name, password)
            assertThat(actual).isEqualTo(expected)
        }
    }
}


