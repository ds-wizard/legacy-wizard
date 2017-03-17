-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Session" cascade;
create table "Session" (
	session_id char(30) primary key,
	user_id int,
	valid_until timestamp with time zone
);
alter table "Session" add constraint "FK_Session_user_id" foreign key (user_id) references "User" (user_id) on update cascade on delete cascade;
alter table "Session" owner to elixir;

