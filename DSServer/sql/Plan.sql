-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Plan";
create table "Plan" (
    id serial primary key,
    user_id int not null references "User"(user_id) on update cascade on delete cascade,
    name text not null,
    description text
);
alter table "Plan" owner to elixir;

