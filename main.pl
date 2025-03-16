:- encoding(utf8).
%%%%%%%%% ОБОЛОЧКА ЭКСПЕРТНОЙ СИСТЕМЫ С МЕХАНИЗМОМ ОБЪЯСНЕНИЯ %%%%%%%%%
% Данный проект представляет один из возможных вариантов оболочки экспертной системы на Прологе.

% Динамические предикаты
:- dynamic is_ans/2.
:- dynamic current_mode/1.
:- dynamic методология/1. % Делаем кредит/1 динамическим для добавления новых правил
:- dynamic stored_proof/1.  % Для хранения объяснения решения

% Определённые инфиксные операторы
:- op(500, xfy, <==).
:- op(500, xfy, /).

:- consult('base.pl').

% Инициализация по умолчанию
:- initialization(assertz(current_mode(expert))).

% Тривиальный случай, когда цель истинна
prove(G, true, _):- G=true,!.

% Обработка дизъюнкции (G1; G2)
prove((G1; G2), P, Q) :- !,
    (prove(G1, P, Q) -> true ; prove(G2, P, Q)).

% Доказать конъюнкцию цели G и конъюнкцию оставшихся целей Gs
prove((G, Gs),(P, Ps),Q) :-!,
    prove(G, P, Q),
    prove(Gs, Ps, Q),!.

% Доказать цель G при условии выполнения конъюнкции подцелей Gs
prove(G, (G <== Ps), Q) :-
    clause(G, Gs),
    prove(Gs, Ps, [G<==Gs|Q]),
    my_asserta(is_ans(G,true)).

% Если уже доказано, что цель G ложна
prove(G, G, _) :-
    is_ans(G,false),!,false.

% Если уже доказано, что цель G истинна
prove(G, G, _) :-
    is_ans(G,true),!,true.

% Если невозможно доказать цель G, спросить у пользователя
prove(G, G, Q) :-
    ask_ans(G,Q),!.

% Формирование запроса к пользователю
ask_ans(G,Q):-
    askable(G),
    ask(G,Answer),
    ans(G,Q,Answer),!.

% Вопрос к пользователю
ask(G,Answer):-
    write("Вопрос: "), write(G), writeln('?'),
    write("Ответ: да/нет/почему/выйти: "),
    flush_output,
    read_line_to_string(user_input, Input),
    atom_string(Answer, Input),
    !.

% Ответ пользователя
ans(G, _, 'да'):- my_asserta(is_ans(G,true)),!.
ans(G, _, 'нет'):- my_asserta(is_ans(G,false)),fail,!.
ans(G, Q,'почему'):-
    Q=[A<==B|_],
    write("Выдвигается гипотеза: "), writeln(A),
    write("при комплексе условий: "), writeln(B),
    write("Ответ: да/нет/почему: "),
    flush_output,
    read_line_to_string(user_input, Input),
    atom_string(Answer, Input),
    ans(G, Q, Answer),!.
ans(_, _, 'выйти'):-
    writeln("Завершение текущего цикла вопросов."),
    retractall(is_ans(_,_)),
    throw(restart).
ans(_, _, _):-fail.

% Сохранение в базе данных
my_asserta(is_ans(G,V)):-retract(is_ans(G,V)),assert(is_ans(G,V)),!.
my_asserta(is_ans(G,V)):-assert(is_ans(G,V)),!.

% Вывод истории
story:-
    writeln("История:"),
    is_ans(G,V),
    write("G = "),write(G),write("  "),
    write("V = "),writeln(V),
    fail.
story:-true.

% Секция запрашиваемых термов
askable(t(бюджет(_))).
askable(t(сроки(_))).
askable(t(ресурсы(_))).
askable(t(опыт_команды(_))).
askable(t(сложность(_))).
askable(t(география(_))).
askable(t(взаимодействие_с_заказчиками(_))).
askable(t(внешние_зависимости(_))).
askable(t(регулируемые_требования(_))).

askable(бюджет(_)).
askable(сроки(_)).
askable(ресурсы(_)).
askable(опыт_команды(_)).
askable(сложность(_)).
askable(география(_)).
askable(взаимодействие_с_заказчиками(_)).
askable(внешние_зависимости(_)).
askable(регулируемые_требования(_)).

% Старт системы с выбором режима
start :-
    writeln("Запуск экспертной системы управления проектами"),
    writeln("Режим работы:"),
    writeln("1 - Режим пользователя"),
    writeln("2 - Режим эксперта"),
    write("Введите номер: "),
    flush_output,
    read_line_to_string(user_input, Input),
    atom_string(ModeStr, Input),
    (   atom_number(ModeStr, Mode), member(Mode, [1, 2])
    ->  set_mode(Mode)
    ;   writeln("Неверный ввод. Установлен режим пользователя по умолчанию."),
        set_mode(1)
    ),
    catch(main_loop, restart, (writeln("Перезапуск системы..."), start)).

% Установка режима
set_mode(1) :-
    retractall(current_mode(_)),
    assertz(current_mode(expert)),
    writeln("Выбран режим пользователя").
set_mode(2) :-
    retractall(current_mode(_)),
    assertz(current_mode(rule_addition)),
    writeln("Выбран режим эксперта").
set_mode(_) :-
    writeln("Неверный выбор. Установлен режим пользователя по умолчанию"),
    retractall(current_mode(_)),
    assertz(current_mode(expert)).

% Главный цикл
main_loop :-
    current_mode(Mode),
    run_mode(Mode).

% Режим эксперта
run_mode(expert) :-
    prove(методология(Решение), Proof, []),
    retractall(stored_proof(_)),  % Очищаем старое объяснение
    assertz(stored_proof(Proof)),  % Сохраняем новое объяснение
    writeln("Решение: "), writeln(Решение),
    writeln("Конец сессии."),
    story,  % Выводим историю автоматически
    writeln("Доступные команды:"),
    writeln("- как"),
    writeln("- история"),
    writeln("- новая_сессия"),
    writeln("- выйти"),
    write("Ввод: "),
    flush_output,
    read_line_to_string(user_input, Input),
    atom_string(Command, Input),
    handle_command(Command).

% Режим добавления правил
run_mode(rule_addition) :-
    writeln("Режим эксперта."),
    writeln("Введите новое правило для предиката методология/1 (заканчивайте правило точкой '.', для выхода введите 'выйти'):"),
    add_rule,
    writeln("Правило добавлено. Добавить ещё? (да/нет/выйти)"),
    flush_output, % Очищаем буфер вывода
    % Читаем и игнорируем возможные остаточные переносы строк
    repeat,
    read_line_to_string(user_input, Input),
    atom_string(Response, Input),
    Response \= '', % Убеждаемся, что строка не пустая
    (   Response = 'да' -> main_loop
    ;   Response = 'выйти' -> throw(restart)
    ;   Response = 'нет' -> throw(restart)
    ;   writeln("Неверный ввод. Пожалуйста, введите 'да', 'нет' или 'выйти'."),
        fail
    ),
    !.

% Добавление правила
add_rule :-
    flush_output,
    read(Rule), % Читаем терм напрямую
    (   Rule = выйти
    ->  throw(restart)
    ;   (   Rule = (методология(Arg) :- Body)
        ->  assertz((методология(Arg) :- Body)),
            write('Parsed rule: '), writeln((методология(Arg) :- Body)),
            writeln("Новое правило добавлено в базу знаний: "), writeln((методология(Arg) :- Body))
        ;   writeln("Ошибка: правило должно иметь следующий вид: методология('...') :- бюджет('...'), сроки('...'), ресурсы('...'), ..."),
            writeln("Попробуйте заново или введите 'выйти'."),
            add_rule
        )
    ).

% Обработка команд пользователя
handle_command('как') :-
    (   stored_proof(Proof)
    ->  writeln("Как получено решение?"), writeln(Proof),
        writeln("Новая сессия."),
        retractall(is_ans(_,_)),
        main_loop
    ;   writeln("Рекомендации отсутствуют."),
        writeln("Новая сессия."),
        retractall(is_ans(_,_)),
        main_loop
    ).
handle_command('история') :-
    story,
    writeln("Новая сессия."),
    retractall(is_ans(_,_)),
    main_loop.
handle_command('новая_сессия') :-
    writeln("Новая сессия."),
    retractall(is_ans(_,_)),
    main_loop.
handle_command('выйти') :-
    writeln("Выход из системы."),
    retractall(is_ans(_,_)),
    throw(exit).
handle_command(_) :-
    writeln("Некорректный ввод."),
    retractall(is_ans(_,_)),
    main_loop.