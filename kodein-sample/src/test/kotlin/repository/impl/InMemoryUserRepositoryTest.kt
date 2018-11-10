package repository.impl

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.repository.impl.InMemoryUserRepository
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

internal class InMemoryUserRepositoryTest {

    val sut = InMemoryUserRepository().also {
        it.createUser(UserName("alice"), Password("open sesame"))
    }

    @Nested
    @DisplayName("IDを指定してユーザーを取得する")
    inner class GetUser {
        @Test
        @DisplayName("正常系")
        fun getUser() {
            // Exercise
            val user = sut.getUser(UserId(1))

            // Verify
            val expected = User(UserId(1), UserName("alice"), Password("open sesame"))
            assertThat(user).isEqualTo(expected)
        }

        @Test
        @DisplayName("存在しないユーザーを取得すると null が返る")
        fun getNonexistentUser() {
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
        fun getUserByName() {
            // Exercise
            val user = sut.getUserByName(UserName("alice"))

            // Verify
            val expected = User(UserId(1), UserName("alice"), Password("open sesame"))
            assertThat(user).isEqualTo(expected)
        }

        @Test
        @DisplayName("存在しないユーザーを取得すると null が返る")
        fun getNonexistentUserByName() {
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
        fun createUser() {
            // Exercise
            val user = sut.createUser(UserName("bob"), Password("secret"))

            // Verify
            val actual = sut.getUser(user.id)
            val expected = User(user.id, UserName("bob"), Password("secret"))
            assertThat(actual).isEqualTo(expected)
        }

        @Test
        @DisplayName("長いユーザー名とパスワードを指定したとき")
        fun longUserNameAndPassword() {
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

