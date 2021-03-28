use mysql;
use mysql::params;
use mysql::prelude::*;
use anyhow::anyhow;

pub struct Wallet {}

impl Wallet {
    // 現在の残高を返す
    pub fn get_balance(&self, tx: &mut mysql::Transaction) -> crate::Result<i64> {
        let user_id: i64 = 1;
        let query = "\
            SELECT `balance` \
              FROM `wallet` \
             WHERE `user_id` = :user_id \
        ";
        let balance: Option<i64> = tx.exec_first(query, params!{
            "user_id" => user_id,
        })?;
        balance.ok_or_else(|| anyhow!("wallet not found: user_id={}", user_id))
    }

    // 残高を減らす
    pub fn pay(&mut self, tx: &mut mysql::Transaction, amount: i64) -> crate::Result<()> {
        let user_id: i64 = 1;
        let stmt = "\
            UPDATE `wallet` \
               SET `balance` = `balance` - :amount \
             WHERE `user_id` = :user_id \
        ";
        tx.exec_drop(stmt, params!{
            "amount" => amount,
            "user_id" => user_id,
        })?;
        Ok(())
    }
}
