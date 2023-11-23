module password

sig Username {}
sig Password {}

sig User {
    , username: one Username
    , password: one Password
}

sig Admin in User {}

fact "unique usernames" {all user: User | no user2: User | user != user2 and user.username = user2.username }

pred CreateUser[admin: Admin] {
    some un: Username - User.username | some user: User - admin | user.username = un
}

pred UpdateUserPassword[admin: Admin, user: User, pwd: Password] {
    user.password = pwd
}

pred RemoveUser[admin: Admin, user: User] {
    no u: User | u = user
}

pred show {
    some admin: Admin | CreateUser[admin]
    some admin: Admin | some user: User - admin | some password: Password | UpdateUserPassword[admin, user, password]
}

run {#Admin = 1} for 9 User, 8 Username, 7 Password