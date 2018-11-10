package com.ynojima.kodeinsample.repository.impl

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.repository.UserRepository

class InMemoryUserRepository : UserRepository {
    private var nextUserId = 1L
    private val users = HashMap<UserId, User>()
    private val nameToUsers = HashMap<UserName, User>()

    override fun getUser(id: UserId) = users[id]

    override fun getUserByName(name: UserName): User? = nameToUsers[name]

    override fun createUser(userName: UserName, password: Password): User {
        val id = UserId(nextUserId)
        nextUserId += 1

        val user = User(id, userName, password)
        users[id] = user
        nameToUsers[user.name] = user

        return user
    }
}
