-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "ActionKey" cascade;
create table "ActionKey" (
	user_id integer,
        action text,
        action_key text unique,
        primary key (user_id, action),
        foreign key (user_id) references "User" on update cascade on delete cascade
);
alter table "ActionKey" owner to elixir;

