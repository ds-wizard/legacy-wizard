-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "ActionKey" cascade;
create table "ActionKey" (
        id serial primary key,
	user_id integer,
        action text,
        action_key text unique,
        created timestamp with time zone not null,
        foreign key (user_id) references "User" on update cascade on delete cascade
);
alter table "ActionKey" owner to elixir;

