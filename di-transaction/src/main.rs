use mysql;
use mysql::params;
use mysql::prelude::*;
use anyhow::anyhow;

type Result<T> = anyhow::Result<T>;

struct Inventory {}

impl Inventory {
    // アイテムを指定された量だけ追加する
    fn add_items(&mut self, tx: &mut mysql::Transaction, amount: i64) -> Result<()> {
        let user_id: i64 = 1;
        let item_id: i64 = 1;
        let stmt = "\
            UPDATE `inventory` \
               SET `amount` = `amount` + :amount \
             WHERE `user_id` = :user_id AND `item_id` = :item_id \
        ";
        tx.exec_drop(stmt, params!{
            "amount" => amount,
            "user_id" => user_id,
            "item_id" => item_id,
        })?;
        Ok(())
    }
}

struct Wallet {}

impl Wallet {
    // 現在の残高を返す
    fn get_balance(&self, tx: &mut mysql::Transaction) -> Result<i64> {
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
    fn pay(&mut self, tx: &mut mysql::Transaction, amount: i64) -> Result<()> {
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

// アイテムを購入する
fn purchase_item(inventory: &mut Inventory, wallet: &mut Wallet, conn: &mut mysql::PooledConn) -> Result<()> {
    let mut tx = conn.start_transaction(mysql::TxOpts::default())?;

    // 残高が十分か確認する
    let current_balance = wallet.get_balance(&mut tx)?;
    if current_balance < 100 {
        return Err(anyhow!("balance is not sufficient: current_balance={}", current_balance));
    }

    // アイテムを追加し、残高を減らす
    inventory.add_items(&mut tx, 1)?;
    wallet.pay(&mut tx, 100)?;

    tx.commit()?;
    Ok(())
}

fn main() -> Result<()> {
    let url = "mysql://root:root@localhost:3306/di_transaction";
    let pool = mysql::Pool::new(url)?;
    let mut conn = pool.get_conn()?;

    let mut inventory = Inventory{};
    let mut wallet = Wallet{};

    purchase_item(&mut inventory, &mut wallet, &mut conn)?;

    Ok(())
}
