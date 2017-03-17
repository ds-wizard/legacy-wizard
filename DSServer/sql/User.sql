-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "User" cascade;
create table "User" (
	user_id serial primary key,
	email varchar(20),
	password_hash varchar(100),
	name varchar(50),
        affiliation varchar(200),
	registration_key char(30) unique,
	registration_confirmed boolean DEFAULT 'f'
);
alter table "User" owner to elixir;

