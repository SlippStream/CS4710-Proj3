module password

/*---------------------------------------- Signatures ----------------------------------------*/

sig Person {}

abstract sig UserAccount {
    , password: one String
    , owner: one Person
    , username: one String
}

sig User extends UserAccount {}

sig Admin in User {}

sig Database {
    , userInDatabase: set UserAccount
}

/*------------------------------------------ Facts ------------------------------------------*/

fact "one database" {
    all u: User | one d: Database | u in d.userInDatabase
    all d: Database | all d2: Database - d | no d.userInDatabase & d2.userInDatabase
}

fact "administrated database" {
    all d: Database | some a: Admin | a in d.userInDatabase
}

fact "unique usernames" {
    all d: Database | all u: d.userInDatabase | no u2: d.userInDatabase - u | u.username = u2.username 
}

fact "no username passwords" {
    all u: UserAccount | u.username != u.password
}

/*---------------------------------------- Functions ----------------------------------------*/

fun adminsInDatabase[d: Database]: set Admin {
    d.userInDatabase & Admin
}

fun nonAdminsInDatabase[d: Database]: set User {
    d.userInDatabase - Admin
}

fun MyDatabaseUsers[u: User]: set User {
    (u.~userInDatabase).userInDatabase
}

fun MultiAccUsers[]: set Person {
    {p: Person | all acc: UserAccount | some acc2: UserAccount | acc.owner = acc2.owner and acc != acc2}
}

/*---------------------------------------- Assertions ----------------------------------------*/

assert no_empty_database {
    all db: Database | some db.userInDatabase
}

assert no_unnacounted_roles {
    all db: Database | db.userInDatabase = (adminsInDatabase[db] + nonAdminsInDatabase[db])
}

assert no_cross_db_users {
    all u: User | lone db: Database | u in db.userInDatabase
}

assert no_lone_users {
    all u: User | some u.~userInDatabase
}
/*---------------------------------------- Predicates ----------------------------------------*/

pred isAdmin[u: User] {
    u in Admin
}

pred isNonAdmin[u: User] {
    u not in Admin
}

//An Admin promotes another user in their database to admin
pred promote[u: User, a: Admin] {
    u in MyDatabaseUsers[a]
    isAdmin[u]
}

//A user changes their password
pred changePassword[u: User, o: Person, newPassword: String] {
    u.owner = o
    newPassword = u.password
} 

//An admin removes a user in their database
pred deleteUser[u: User, a: Admin] {
    u not in MyDatabaseUsers[a]
}

//A user deletes their own account
pred deleteUser[un: String, pass: String, d: Database] {
    no u: d.userInDatabase | u.username = un and pass = u.password
}

//A user logs is able to log into their account
pred login[un: String, pass: String, db: Database] {
    some user: User | user in db.userInDatabase and user.username = un and user.password = pass
}

//A person creates an account in a database
pred createAccount[acc: UserAccount, d: Database] {
    some u: User {
        acc in u
        u in d.userInDatabase
    }
}



pred create_and_login {
    some acc: UserAccount | some d: Database {
        createAccount[acc, d]
        login[acc.username, acc.password, d]
    }
}

pred admin_promotes {
    some a: Admin {
        some u: User - a {
            u in MyDatabaseUsers[a]
            promote[u, a]
        }
    }
}

pred user_deletes {
    some acc: UserAccount| some d:Database {
        deleteUser[acc.username, acc.password, d]
    }
}

pred admin_deletes {
    some a: Admin | some u: User - a {
        deleteUser[u, a]
    }   
}

pred show{
}

run admin_deletes for 8 User, exactly 2 Database, exactly 7 String, exactly 7 Person


