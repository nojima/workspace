CREATE DATABASE IF NOT EXISTS di_transaction;
USE di_transaction;

CREATE TABLE IF NOT EXISTS `inventory` (
    `user_id` BIGINT NOT NULL,
    `item_id` BIGINT NOT NULL,
    `amount` BIGINT NOT NULL,
    PRIMARY KEY (`user_id`, `item_id`)
);

CREATE TABLE IF NOT EXISTS `wallet` (
    `user_id` BIGINT NOT NULL,
    `balance` BIGINT NOT NULL,
    PRIMARY KEY (`user_id`)
);
