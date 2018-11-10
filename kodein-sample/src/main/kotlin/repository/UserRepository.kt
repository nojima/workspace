package com.ynojima.kodeinsample.repository

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName

interface UserRepository {
    fun getUser(id: UserId): User?
    fun getUserByName(name: UserName): User?
    fun createUser(userName: UserName, password: Password): User
}
