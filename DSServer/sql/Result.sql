-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Result";
create table "Result" (
    id serial primary key,
    plan_id int not null references "Plan"(id) on update cascade on delete cascade,
    name text not null,
    rid text,
    text text,
    value text,
    constraint uniq_result unique (plan_id, name)
);
alter table "Result" owner to elixir;

