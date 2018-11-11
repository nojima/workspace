package com.ynojima.kodeinsample.repository.impl

import com.ynojima.kodeinsample.Password
import com.ynojima.kodeinsample.User
import com.ynojima.kodeinsample.UserId
import com.ynojima.kodeinsample.UserName
import com.ynojima.kodeinsample.repository.UserRepository
import kotliquery.TransactionalSession
import kotliquery.queryOf

class MySqlUserRepository(
    val tx: TransactionalSession
): UserRepository {

    override fun createUser(userName: UserName, password: Password): User {
        val insertQuery = queryOf(
            "INSERT INTO `users` (`name`, `password`) VALUES (?, ?)",
            userName.toString(),
            password.toString()
        ).asUpdate
        tx.run(insertQuery)

        val selectQuery = queryOf(
            "SELECT LAST_INSERT_ID()"
        ).map { row ->
            row.long(1)
        }.asSingle
        val userId = UserId(tx.run(selectQuery)!!)

        return User(userId, userName, password)
    }

    override fun getUser(id: UserId): User? {
        val query = queryOf(
            "SELECT `name`, `password` FROM `users` WHERE `id` = ?",
            id.toLong()
        ).map { row ->
            User(id, UserName(row.string(1)), Password(row.string(2)))
        }.asSingle
        return tx.run(query)
    }

    override fun getUserByName(name: UserName): User? {
        val query = queryOf(
            "SELECT `id`, `password` FROM `users` WHERE `name` = ?",
            name.toString()
        ).map { row ->
            User(UserId(row.long(1)), name, Password(row.string(2)))
        }.asSingle
        return tx.run(query)
    }
}
