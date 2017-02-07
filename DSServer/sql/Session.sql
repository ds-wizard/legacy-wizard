-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Session" cascade;
create table "Session" (
	session_id uuid primary key,
	user_id int,
	valid_until timestamp
);
alter table "Session" owner to elixir;

