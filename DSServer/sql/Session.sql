-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Session" cascade;
create table "Session" (
	session_id char(10) primary key,
	user_id int,
	valid_until timestamp with time zone
);
alter table "Session" owner to elixir;

