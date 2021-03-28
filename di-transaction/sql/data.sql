USE di_transaction;

BEGIN;

INSERT INTO `wallet` (`user_id`, `balance`)
VALUES (1, 150)
ON DUPLICATE KEY UPDATE `balance` = 150;

INSERT INTO `inventory` (`user_id`, `item_id`, `amount`)
VALUES (1, 1, 0)
ON DUPLICATE KEY UPDATE `amount` = 0;

COMMIT;
