/**
 * One-paragraph orientation block rendered at the top of every overview page.
 *
 * Intended for first-time readers: what is this view, what question does it
 * answer, how should I read the visualizations below. Keep it short — 2 to 4
 * sentences. Longer elaboration belongs in SectionCard subtitles.
 */

import { ParentComponent } from 'solid-js';

const Intro: ParentComponent = (props) => {
  return (
    <div class="max-w-3xl text-[15px] text-gray-700 dark:text-gray-300 leading-relaxed">
      {props.children}
    </div>
  );
};

export default Intro;
