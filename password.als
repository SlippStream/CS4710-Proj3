module password

sig Person {}

abstract sig User {
    , password: one String
    , owner: one Person
}

sig UserAccount extends User {}

sig Admin in UserAccount {}

sig Database {
    , userInDatabase: set User
}

pred login[user: User, db: Database, pass: String] {
    user in db.userInDatabase
    user.password = pass
}

pred show{
    some u: User | some p: String | some d: Database | login[u,d,p]
}

fact "one database" {
    all u: User | one d: Database | u in d.userInDatabase
    all d: Database | all d2: Database - d | no d.userInDatabase & d2.userInDatabase
}

fact "administrated database" {
    all d: Database | some a: Admin | a in d.userInDatabase
}

run show for 8 User, 2 Database, exactly 8 String, exactly 5 Person
