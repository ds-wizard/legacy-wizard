-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Plan";
create table "Plan" (
    id serial primary key,
    user_id int not null references "User"(user_id) on update cascade on delete cascade,
    name varchar(50) not null,
    description varchar(1000)
);
alter table "Plan" owner to elixir;

